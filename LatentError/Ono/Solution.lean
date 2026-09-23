import Mathlib

open scoped BigOperators Topology Matrix MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter

noncomputable section

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

/-! ## Definition 2 (The three assumed background facts). -/

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

/-! ## Definition 3 (Asymptotic model realization — the hypothesis bundle).

An instance records the deterministic consequences (fields 1--7), valid on the
almost-sure event of Proposition 1 and Lemma 5, for one fixed realization of the
factor path `F` and noise array.  Data are indexed by the admissible cross-section
sizes `Adm k = {p : ℕ // k ≤ p}`, with `k, n, δ²` fixed. -/

/-- Admissible cross-section sizes `p ≥ k`.  Admissibility is part of the index:
no `p × k` matrix with `p < k` can have `k` orthonormal columns, so the structural
fields below are stated unconditionally over `Adm k`, and asymptotic limits are
taken along `atTop` on `Adm k`. -/
abbrev Adm (k : ℕ) := {p : ℕ // k ≤ p}

/-- The asymptotic factor-model bundle (Definition 3).

Abbreviations used below (all derived from the fields):
* `Y P = b P * Φ P + Z P`               (the data matrix `Y = bΦ + Z ∈ ℝ^{p×n}`),
* `S P = (1/(np)) • (Y P) (Y P)ᵀ`       (scaled sample covariance `S^{(p,n)} ∈ ℝ^{p×p}`),
* `W P = (1/(np)) • (Y P)ᵀ (Y P)`       (dual `W^{(p,n)} ∈ ℝ^{n×n}`),
* `Npn P = (1/(np)) • (Φ P) (Φ P)ᵀ`     (`N^{(p,n)} ∈ ℝ^{k×k}`),
* `Sig0 P = (B P) Σ_f (B P)ᵀ`           (population `Σ₀ = B Σ_f Bᵀ ∈ ℝ^{p×p}`),
* `Wn0 = (1/n) • Fᵀ G_B F`              (`W^{(n),0} ∈ ℝ^{n×n}`),
* `Nn = (1/n) • Φ̄∞ (Φ̄∞)ᵀ`             (`N^{(n)} ∈ ℝ^{k×k}`). -/
structure AsymptoticModel (k n : ℕ) (δ2 : ℝ) where
  /-- `1 ≤ k`. -/
  hk : 1 ≤ k
  /-- `k < n`. -/
  hkn : k < n
  /-- `δ² > 0`. -/
  hδ2 : 0 < δ2
  -- Data (indexed by the admissible cross-section size `P : Adm k`):
  /-- `B(p) ∈ ℝ^{p×k}`. -/
  B : (P : Adm k) → Matrix (Fin P.1) (Fin k) ℝ
  /-- fixed `Σ_f ∈ ℝ^{k×k}`, symmetric positive definite. -/
  Sf : Matrix (Fin k) (Fin k) ℝ
  /-- `b(p) ∈ ℝ^{p×k}` with orthonormal columns (`bᵀ b = Iₖ`); its columns are the
  estimation targets. -/
  b : (P : Adm k) → Matrix (Fin P.1) (Fin k) ℝ
  /-- the fixed (`p`-free) factor path `F ∈ ℝ^{k×n}`. -/
  F : Matrix (Fin k) (Fin n) ℝ
  /-- `Φ(p) ∈ ℝ^{k×n}` with `B F = b Φ`; `Φ̄(p) := Φ(p)/√p`. -/
  Φ : (P : Adm k) → Matrix (Fin k) (Fin n) ℝ
  /-- `Z(p) ∈ ℝ^{p×n}` (noise). -/
  Z : (P : Adm k) → Matrix (Fin P.1) (Fin n) ℝ
  /-- `hⱼ = h(p,j) ∈ ℝ^p`, the `j`-th unit eigenvector of `S^{(p,n)}` (top-`k`, in
  decreasing eigenvalue order). -/
  h : (P : Adm k) → Fin k → EuclideanSpace ℝ (Fin P.1)
  /-- `wⱼ^{(p,n)} ∈ ℝ^n`, unit eigenvector of `W^{(p,n)}` at `θⱼ^{(p,n)}`. -/
  w : (P : Adm k) → Fin k → EuclideanSpace ℝ (Fin n)
  /-- `νⱼ^{(p)} ∈ ℝ^k`, `j`-th unit eigenvector of `N^{(p,n)}`. -/
  ν : (P : Adm k) → Fin k → EuclideanSpace ℝ (Fin k)
  /-- the full sorted eigenvalue list `θ₁^{(p,n)} ≥ ⋯ ≥ θₙ^{(p,n)}` of `W^{(p,n)}`. -/
  θ : (P : Adm k) → Fin n → ℝ
  /-- the eigenvalues `νval P j` of `N^{(p,n)}` attached to the ordered eigenvectors
  `ν P j` (weakly decreasing). -/
  νval : (P : Adm k) → Fin k → ℝ
  -- Limiting objects (fixed, `p`-free):
  /-- `Φ̄∞ ∈ ℝ^{k×n}`. -/
  Φbarinf : Matrix (Fin k) (Fin n) ℝ
  /-- `G_B ∈ ℝ^{k×k}`, the limit of `Bᵀ B/p`. -/
  GB : Matrix (Fin k) (Fin k) ℝ
  /-- eigenvalues `λⱼ^{(n)}` (`j = 1,…,k`). -/
  lam : Fin k → ℝ
  /-- unit eigenvectors `wⱼ^{(n)} ∈ ℝ^n` of `W^{(n),0} = Fᵀ G_B F/n`. -/
  wn : Fin k → EuclideanSpace ℝ (Fin n)
  /-- unit eigenvectors `νⱼ^{(n)} ∈ ℝ^k` of `N^{(n)} = Φ̄∞ (Φ̄∞)ᵀ/n`. -/
  νn : Fin k → EuclideanSpace ℝ (Fin k)
  -- ===== Standing structural hypotheses on the data (unconditional over `Adm k`) =====
  /-- `bᵀ b = Iₖ` (orthonormal columns). -/
  hb_ortho : ∀ P : Adm k, (b P)ᵀ * (b P) = 1
  /-- `B(p)` has full column rank `k`. -/
  hB_rank : ∀ P : Adm k, (B P).rank = k
  /-- `col(b) = col(B)`: the two matrices have the same column space (equal ranges of
  their transpose-actions on Euclidean space). -/
  hcol_eq : ∀ P : Adm k,
    LinearMap.range (Matrix.toEuclideanLin (B P)) =
      LinearMap.range (Matrix.toEuclideanLin (b P))
  /-- `B F = b Φ`. -/
  hBF : ∀ P : Adm k, (B P) * F = (b P) * (Φ P)
  /-- `Σ_f` symmetric positive definite. -/
  hSf : Sf.PosDef
  /-- `G_B` positive definite. -/
  hGB : GB.PosDef
  /-- `SfSqrt = Σ_f^{1/2}`, the positive-semidefinite square root of `Σ_f`, recorded
  abstractly by its defining properties (positive-semidefinite, square equals `Σ_f`),
  which uniquely characterize the PSD square root of the positive-definite `Σ_f`. -/
  SfSqrt : Matrix (Fin k) (Fin k) ℝ
  hSfSqrt_psd : SfSqrt.PosSemidef
  hSfSqrt_sq : SfSqrt * SfSqrt = Sf
  /-- The population matrix `Σ_f^{1/2} G_B Σ_f^{1/2}` is Hermitian with *distinct*
  positive eigenvalues (Lemma 2 / Assumption 4).  Distinctness is expressed as
  injectivity of the eigenvalue enumeration. -/
  hSfGB_herm : (SfSqrt * GB * SfSqrt).IsHermitian
  hSfGB_posDef : (SfSqrt * GB * SfSqrt).PosDef
  hSfGB_distinct : Function.Injective hSfGB_herm.eigenvalues
  -- ===== Population eigenstructure of `Σ₀(p) = B(p) Σ_f B(p)ᵀ` (field 7) =====
  /-- Population eigenvalues `σ₀ⱼ(p)` of `Σ₀(p) = B(p) Σ_f B(p)ᵀ` (top `k`), strictly
  decreasing and positive; `p`-dependent. -/
  sig0 : (P : Adm k) → Fin k → ℝ
  hsig0_pos : ∀ P : Adm k, ∀ j, 0 < sig0 P j
  hsig0_sorted : ∀ P : Adm k, StrictAnti (sig0 P)
  /-- The columns `b₁, …, b_k` are ordered orthonormal unit eigenvectors of
  `Σ₀(p) = B(p) Σ_f B(p)ᵀ` at the eigenvalues `σ₀ⱼ(p)`. -/
  hb_eig : ∀ P : Adm k, ∀ j : Fin k,
    Matrix.toEuclideanLin ((B P) * Sf * (B P)ᵀ) (colVec (b P) j)
      = sig0 P j • colVec (b P) j
  -- ===== Ordering / eigenvector fields on `θ, h, w, ν` (fields 4,5,7) =====
  /-- The full dual spectrum `θ P` is weakly decreasing. -/
  hθ_sorted : ∀ P : Adm k, Antitone (θ P)
  /-- `θ P` is the *complete* sorted eigenvalue list of `W^{(p,n)} = Yᵀ Y/(np)`:
  it is a permutation `e` of the Hermitian eigenvalues of `W^{(p,n)}`.  Together with
  `hθ_sorted` this pins `θ P` to be exactly the weakly-decreasing list of all `n`
  eigenvalues of `W^{(p,n)}`. -/
  hθ_spectrum : ∀ P : Adm k,
    ∃ (hW : ((1 / ((n : ℝ) * P.1)) •
        (((b P) * (Φ P) + Z P)ᵀ * ((b P) * (Φ P) + Z P))).IsHermitian)
      (e : Fin n ≃ Fin n), θ P = fun i => hW.eigenvalues (e i)
  /-- Each `hⱼ` is a unit vector. -/
  hh_unit : ∀ P : Adm k, ∀ j, ‖h P j‖ = 1
  /-- The columns `h₁, …, h_k` are pairwise orthonormal (so `H` has `k` orthonormal
  columns).  Encoded as `Hᵀ H = Iₖ`. -/
  hH_ortho : ∀ P : Adm k, (Hmat (h P))ᵀ * (Hmat (h P)) = 1
  /-- `hⱼ` is the `j`-th (top-`k`, decreasing order) unit eigenvector of
  `S^{(p,n)} = Y Yᵀ/(np)` at eigenvalue `θⱼ^{(p,n)}` (index `j` cast into `Fin n`). -/
  hh_eig : ∀ P : Adm k, ∀ j : Fin k,
    Matrix.toEuclideanLin
        ((1 / ((n : ℝ) * P.1)) • (((b P) * (Φ P) + Z P) * ((b P) * (Φ P) + Z P)ᵀ))
        (h P j)
      = θ P (Fin.castLE (le_of_lt hkn) j) • (h P j)
  /-- Each `wⱼ^{(p,n)}` is a unit vector. -/
  hw_unit : ∀ P : Adm k, ∀ j, ‖w P j‖ = 1
  /-- `wⱼ^{(p,n)}` is a unit eigenvector of `W^{(p,n)} = Yᵀ Y/(np)` at its `j`-th
  largest eigenvalue `θⱼ^{(p,n)}`. -/
  hw_eig : ∀ P : Adm k, ∀ j : Fin k,
    Matrix.toEuclideanLin
        ((1 / ((n : ℝ) * P.1)) • (((b P) * (Φ P) + Z P)ᵀ * ((b P) * (Φ P) + Z P)))
        (w P j)
      = θ P (Fin.castLE (le_of_lt hkn) j) • (w P j)
  /-- Each `νⱼ^{(p)}` is a unit vector. -/
  hν_unit : ∀ P : Adm k, ∀ j, ‖ν P j‖ = 1
  /-- The finite-`p` eigenvalues `νval P` (of `N^{(p,n)}`) are weakly decreasing, so
  `ν P` is an *ordered* eigenvector family. -/
  hνval_sorted : ∀ P : Adm k, Antitone (νval P)
  /-- `νⱼ^{(p)}` is the `j`-th (decreasing order) unit eigenvector of
  `N^{(p,n)} = ΦΦᵀ/(np)` at eigenvalue `νval P j`. -/
  hν_eig : ∀ P : Adm k, ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / ((n : ℝ) * P.1)) • ((Φ P) * (Φ P)ᵀ)) (ν P j)
      = νval P j • (ν P j)
  -- ===== Limiting eigenpair structure (fields 5,6,7 limits) =====
  /-- strict ordering `λ₁^{(n)} > ⋯ > λₖ^{(n)} > 0` (Assumption 5). -/
  hlam_pos : ∀ j, 0 < lam j
  hlam_sorted : StrictAnti lam
  /-- each `wⱼ^{(n)}` a unit vector. -/
  hwn_unit : ∀ j, ‖wn j‖ = 1
  /-- each `νⱼ^{(n)}` a unit vector. -/
  hνn_unit : ∀ j, ‖νn j‖ = 1
  /-- `wⱼ^{(n)}` is the `j`-th unit eigenvector of `W^{(n),0} = Fᵀ G_B F/n` at
  eigenvalue `λⱼ^{(n)}`. -/
  hwn_eig : ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / (n : ℝ)) • (Fᵀ * GB * F)) (wn j) = lam j • (wn j)
  /-- `νⱼ^{(n)}` is the `j`-th unit eigenvector of `N^{(n)} = Φ̄∞ (Φ̄∞)ᵀ/n` at
  eigenvalue `λⱼ^{(n)}`. -/
  hνn_eig : ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / (n : ℝ)) • (Φbarinf * Φbarinfᵀ)) (νn j)
      = lam j • (νn j)
  -- ===== Fields (deterministic conclusions of Proposition 1 and Lemma 5) =====
  /-- Field 1 — Noise Gram limit (Prop. 1(a)): `Zᵀ Z/(np) → (δ²/n) Iₙ`. -/
  field1_noiseGram :
    Tendsto (fun P : Adm k => (1 / ((n : ℝ) * P.1)) • ((Z P)ᵀ * (Z P))) atTop
      (𝓝 ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ)))
  /-- Field 2 — Projected-noise decoherence (Prop. 1(b) / Lemma 3):
  `(1/√p) bᵀ(p) Z(p) → 0` in `ℝ^{k×n}`. -/
  field2_decoherence :
    Tendsto (fun P : Adm k => (1 / Real.sqrt P.1) • ((b P)ᵀ * (Z P))) atTop
      (𝓝 (0 : Matrix (Fin k) (Fin n) ℝ))
  /-- Field 3 — Signal-coordinate matrix limit (Lemma 5(ii)):
  `Φ̄(p) = Φ(p)/√p → Φ̄∞`. -/
  field3_signalLimit :
    Tendsto (fun P : Adm k => (1 / Real.sqrt P.1) • (Φ P)) atTop (𝓝 Φbarinf)
  /-- Field 4a — Dual spectrum limits (Prop. 1(c)): for `j = 1,…,k`,
  `θⱼ^{(p,n)} → λⱼ^{(n)} + δ²/n`. -/
  field4_dualSpectrum :
    ∀ j : Fin k, Tendsto (fun P : Adm k => θ P (Fin.castLE (le_of_lt hkn) j)) atTop
      (𝓝 (lam j + δ2 / n))
  /-- Field 4b — the trailing (bulk) average `ℓ^{(p,n)} := (1/(n−k)) Σ_{i=k+1}^n
  θᵢ^{(p,n)}` tends to `δ²/n`. -/
  field4_trailing :
    Tendsto (fun P : Adm k => (1 / ((n : ℝ) - k)) *
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), θ P i) atTop
      (𝓝 (δ2 / n))
  /-- Field 5 — Dual eigenvector convergence (Prop. 1(d)): `wⱼ^{(p,n)} → wⱼ^{(n)}`. -/
  field5_dualEigvec : ∀ j : Fin k, Tendsto (fun P : Adm k => w P j) atTop (𝓝 (wn j))
  /-- Field 6a — Duality link (Lemma 5(iii)):
  `Φ̄∞ wⱼ^{(n)} = √(n λⱼ^{(n)}) · νⱼ^{(n)}`. -/
  field6_duality : ∀ j : Fin k,
    Matrix.toEuclideanLin Φbarinf (wn j) = Real.sqrt (n * lam j) • (νn j)
  /-- Field 6b — `νⱼ^{(p)} → νⱼ^{(n)}`. -/
  field6_nuLimit : ∀ j : Fin k, Tendsto (fun P : Adm k => ν P j) atTop (𝓝 (νn j))
  /-- Field 7a — Population structure: `Bᵀ B/p → G_B`. -/
  field7_BtB : Tendsto (fun P : Adm k => (1 / (P.1 : ℝ)) • ((B P)ᵀ * (B P))) atTop (𝓝 GB)

/-! ## Helper lemmas -/

/-- `colVec M j = toEuclideanLin M (single j 1)`. -/
private lemma colVec_eq_toEuclideanLin {p k : ℕ} (M : Matrix (Fin p) (Fin k) ℝ) (j : Fin k) :
    colVec M j = Matrix.toEuclideanLin M (EuclideanSpace.single j (1 : ℝ)) := by
  ext i
  simp only [colVec, Matrix.toEuclideanLin_apply]
  rw [EuclideanSpace.ofLp_single, Matrix.mulVec_single_one]
  simp [Matrix.col_apply]

/-- A matrix `b` with orthonormal columns (`bᵀ b = I`) induces an inner-product
preserving map on Euclidean space. -/
private lemma inner_toEuclideanLin_ortho {p k : ℕ} (b : Matrix (Fin p) (Fin k) ℝ)
    (hb : bᵀ * b = 1) (x y : EuclideanSpace ℝ (Fin k)) :
    (inner ℝ (Matrix.toEuclideanLin b x) (Matrix.toEuclideanLin b y) : ℝ)
      = inner ℝ x y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.piLp_ofLp_toEuclideanLin, Matrix.piLp_ofLp_toEuclideanLin]
  simp only [Matrix.toLin'_apply, star_trivial]
  rw [Matrix.dotProduct_mulVec]
  rw [show (b *ᵥ WithLp.ofLp y) ᵥ* b = (bᵀ * b) *ᵥ WithLp.ofLp y from ?_]
  · rw [hb]; simp
  · rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]

/-- Norm preservation from `bᵀ b = I`. -/
private lemma norm_toEuclideanLin_ortho {p k : ℕ} (b : Matrix (Fin p) (Fin k) ℝ)
    (hb : bᵀ * b = 1) (x : EuclideanSpace ℝ (Fin k)) :
    ‖Matrix.toEuclideanLin b x‖ = ‖x‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (Matrix.toEuclideanLin b x)),
      ← Real.sqrt_sq (norm_nonneg x)]
  congr 1
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  exact inner_toEuclideanLin_ortho b hb x x

/-! ## Shared auxiliary lemmas for the asymptotic theorems. -/

/-- **sinSq for unit vectors.**  For unit `u, v`, `sinSq u v = 1 − ⟨u,v⟩²`. -/
private lemma sinSq_of_unit {m : ℕ} {u v : EuclideanSpace ℝ (Fin m)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    sinSq u v = 1 - (inner ℝ u v : ℝ) ^ 2 := by
  simp [sinSq, hu, hv]

/-- **sinSq is nonnegative for unit vectors.**  Cauchy–Schwarz gives `⟨u,v⟩² ≤ 1`. -/
private lemma sinSq_nonneg_unit {m : ℕ} {u v : EuclideanSpace ℝ (Fin m)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    0 ≤ sinSq u v := by
  rw [sinSq_of_unit hu hv]
  have h := abs_real_inner_le_norm u v
  rw [hu, hv] at h
  have h2 : (inner ℝ u v : ℝ) ^ 2 ≤ 1 := by
    have habs : |(inner ℝ u v : ℝ)| ≤ 1 := by simpa using h
    nlinarith [abs_nonneg (inner ℝ u v : ℝ), sq_abs (inner ℝ u v : ℝ)]
  linarith

/-- **Continuity of `sinSq` in both arguments along a filter, for unit vectors.**
If `uₚ → u`, `vₚ → v` with `u, v` unit, then `sinSq uₚ vₚ → sinSq u v`.  Used to
transfer the finite-`p` `sinSq` to its limit. -/
private lemma sinSq_tendsto {m : ℕ} {ι : Type*} {L : Filter ι}
    {up : ι → EuclideanSpace ℝ (Fin m)} {vp : ι → EuclideanSpace ℝ (Fin m)}
    {u v : EuclideanSpace ℝ (Fin m)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hup : Tendsto up L (𝓝 u)) (hvp : Tendsto vp L (𝓝 v)) :
    Tendsto (fun i => sinSq (up i) (vp i)) L (𝓝 (sinSq u v)) := by
  unfold sinSq
  have hinner : Tendsto (fun i => (inner ℝ (up i) (vp i) : ℝ)) L (𝓝 (inner ℝ u v)) :=
    hup.inner hvp
  have hnu : Tendsto (fun i => ‖up i‖) L (𝓝 ‖u‖) := hup.norm
  have hnv : Tendsto (fun i => ‖vp i‖) L (𝓝 ‖v‖) := hvp.norm
  have hden : Tendsto (fun i => ‖up i‖ ^ 2 * ‖vp i‖ ^ 2) L (𝓝 (‖u‖ ^ 2 * ‖v‖ ^ 2)) :=
    (hnu.pow 2).mul (hnv.pow 2)
  have hden_ne : (‖u‖ ^ 2 * ‖v‖ ^ 2) ≠ 0 := by rw [hu, hv]; norm_num
  have hnum : Tendsto (fun i => (inner ℝ (up i) (vp i) : ℝ) ^ 2) L
      (𝓝 ((inner ℝ u v : ℝ) ^ 2)) := hinner.pow 2
  exact (tendsto_const_nhds).sub (hnum.div hden hden_ne)

/-- **`sinSq` is invariant under nonzero scaling of the first argument.** -/
private lemma sinSq_smul_left {m : ℕ} (a : ℝ) (ha : a ≠ 0)
    (u v : EuclideanSpace ℝ (Fin m)) :
    sinSq (a • u) v = sinSq u v := by
  unfold sinSq
  rw [inner_smul_left, norm_smul]
  simp only [RCLike.conj_to_real, Real.norm_eq_abs]
  rw [mul_pow, mul_pow, sq_abs]
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  congr 1
  by_cases hden : ‖u‖ ^ 2 * ‖v‖ ^ 2 = 0
  · rw [hden]
    rw [show a ^ 2 * ‖u‖ ^ 2 * ‖v‖ ^ 2 = a ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2) by ring, hden]
    simp
  · rw [mul_assoc, mul_div_mul_left _ _ ha2]

/-- **Continuity of `sinSq` for nonzero (not necessarily unit) limits.**  If
`uₚ → u`, `vₚ → v` with `u ≠ 0`, `v ≠ 0`, then `sinSq uₚ vₚ → sinSq u v`. -/
private lemma sinSq_tendsto' {m : ℕ} {ι : Type*} {L : Filter ι}
    {up : ι → EuclideanSpace ℝ (Fin m)} {vp : ι → EuclideanSpace ℝ (Fin m)}
    {u v : EuclideanSpace ℝ (Fin m)}
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hup : Tendsto up L (𝓝 u)) (hvp : Tendsto vp L (𝓝 v)) :
    Tendsto (fun i => sinSq (up i) (vp i)) L (𝓝 (sinSq u v)) := by
  unfold sinSq
  have hinner : Tendsto (fun i => (inner ℝ (up i) (vp i) : ℝ)) L (𝓝 (inner ℝ u v)) :=
    hup.inner hvp
  have hnu : Tendsto (fun i => ‖up i‖) L (𝓝 ‖u‖) := hup.norm
  have hnv : Tendsto (fun i => ‖vp i‖) L (𝓝 ‖v‖) := hvp.norm
  have hden : Tendsto (fun i => ‖up i‖ ^ 2 * ‖vp i‖ ^ 2) L (𝓝 (‖u‖ ^ 2 * ‖v‖ ^ 2)) :=
    (hnu.pow 2).mul (hnv.pow 2)
  have hunz : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hvnz : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hden_ne : (‖u‖ ^ 2 * ‖v‖ ^ 2) ≠ 0 := by positivity
  have hnum : Tendsto (fun i => (inner ℝ (up i) (vp i) : ℝ) ^ 2) L
      (𝓝 ((inner ℝ u v : ℝ) ^ 2)) := hinner.pow 2
  exact (tendsto_const_nhds).sub (hnum.div hden hden_ne)

/-! ## Main Statements

Throughout, `hFact1`, `hFact2 m`, `hFact3 m` are the hypotheses that Facts 1, 2, 3
hold (Definition 2), appearing at the indicated dimension(s). -/

/-- Abbreviation: the data matrix `Y = bΦ + Z` for the model `M` at index `P`. -/
private def Ymat {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) (P : Adm k) :
    Matrix (Fin P.1) (Fin n) ℝ := (M.b P) * (M.Φ P) + M.Z P

/-- Composition of `toEuclideanLin`: `M (A v) = (M*A) v`. -/
private lemma toEuclideanLin_comp {p q r : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Matrix (Fin q) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin r)) :
    Matrix.toEuclideanLin M (Matrix.toEuclideanLin A v)
      = Matrix.toEuclideanLin (M * A) v := by
  ext i
  simp only [Matrix.toEuclideanLin_apply]
  rw [Matrix.mulVec_mulVec]

/-- `‖toEuclideanLin M v‖² = ⟨v, toEuclideanLin (Mᵀ*M) v⟩` (real). -/
private lemma normSq_toEuclideanLin {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (v : EuclideanSpace ℝ (Fin q)) :
    ‖Matrix.toEuclideanLin M v‖ ^ 2
      = (inner ℝ v (Matrix.toEuclideanLin (Mᵀ * M) v) : ℝ) := by
  rw [← real_inner_self_eq_norm_sq]
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.ofLp_toEuclideanLin_apply, Matrix.ofLp_toEuclideanLin_apply]
  simp only [star_trivial]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm]

/-- **Simplicity ⇒ 1-dim eigenspace.**  Abstract spectral fact: for a Hermitian
`n×n` matrix `A`, if `w` is a unit eigenvector at eigenvalue `μ` and `μ` occurs
*only once* in the (index-`i₀`) enumeration of eigenvalues — i.e. every unit
eigenvector at `μ` is `±w` (`μ` is a simple eigenvalue) — then every vector `v`
with `A v = μ v` is a scalar multiple of `w`.

Here simplicity is packaged in the directly usable form: any unit eigenvector at
`μ` equals `±w`.  From this, any `v` with `A v = μ v` is `c • w` (if `v = 0` take
`c = 0`; else normalize `v/‖v‖`, a unit eigenvector, hence `±w`, so `v = ±‖v‖ • w`). -/
private lemma eigenvector_parallel_of_simple {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (w v : EuclideanSpace ℝ (Fin n))
    (hw : ‖w‖ = 1)
    (hsimple : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
      Matrix.toEuclideanLin A u = μ • u → u = w ∨ u = -w)
    (hv : Matrix.toEuclideanLin A v = μ • v) :
    ∃ c : ℝ, v = c • w := by
  by_cases hv0 : v = 0
  · exact ⟨0, by rw [hv0, zero_smul]⟩
  · have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    set u : EuclideanSpace ℝ (Fin n) := (‖v‖)⁻¹ • v with hudef
    have hun : ‖u‖ = 1 := by
      rw [hudef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
      field_simp
    have hue : Matrix.toEuclideanLin A u = μ • u := by
      rw [hudef, map_smul, hv, smul_comm]
    have hvu : v = ‖v‖ • u := by
      rw [hudef, smul_smul, mul_inv_cancel₀ hvn, one_smul]
    rcases hsimple u hun hue with h | h
    · refine ⟨‖v‖, ?_⟩
      calc v = ‖v‖ • u := hvu
        _ = ‖v‖ • w := by rw [h]
    · refine ⟨-‖v‖, ?_⟩
      calc v = ‖v‖ • u := hvu
        _ = ‖v‖ • (-w) := by rw [h]
        _ = -‖v‖ • w := by rw [smul_neg, neg_smul]

/-- **Abstract spectral simplicity ⇒ ±.**  For a real Hermitian `n×n` matrix `A`,
if the eigenvalue `μ` occurs at a unique index `i₀` of the eigenvalue enumeration
(`hsep`: every other index has a different eigenvalue), then any two unit
eigenvectors of `A` at `μ` agree up to sign.  This is the spectral-theorem core of
`floor_W_simple`: expand both unit eigenvectors in the orthonormal
`eigenvectorBasis`; the eigen-equation forces every coordinate at an index `i ≠ i₀`
to vanish, so both vectors are scalar multiples of the single basis vector
`eigenvectorBasis i₀`; equal norms ⇒ the scalars have equal absolute value ⇒ `±`. -/
private lemma hermitian_simple_eigvec_pm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (i₀ : Fin n) (μ : ℝ)
    (hμ : hA.eigenvalues i₀ = μ)
    (hsep : ∀ i : Fin n, i ≠ i₀ → hA.eigenvalues i ≠ μ)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1)
    (hwe : Matrix.toEuclideanLin A w = μ • w)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1)
    (hue : Matrix.toEuclideanLin A u = μ • u) :
    u = w ∨ u = -w := by
  classical
  set eb := hA.eigenvectorBasis with hebdef
  -- eigen-equation for basis vectors in Euclidean form
  have heig : ∀ i, Matrix.toEuclideanLin A (eb i) = hA.eigenvalues i • (eb i) := by
    intro i
    have h1 : Matrix.toEuclideanLin A (eb i) = WithLp.toLp 2 (A *ᵥ WithLp.ofLp (eb i)) :=
      Matrix.toEuclideanLin_apply A (eb i)
    rw [h1, hA.mulVec_eigenvectorBasis i]
    rfl
  -- self-adjointness of toEuclideanLin A
  have hsymm : (Matrix.toEuclideanLin A).IsSymmetric :=
    (Matrix.isHermitian_iff_isSymmetric).mp hA
  -- key claim: for any x with toEuclideanLin A x = μ • x, and i ≠ i₀, ⟨eb i, x⟩ = 0
  have hclaim : ∀ (x : EuclideanSpace ℝ (Fin n)),
      Matrix.toEuclideanLin A x = μ • x →
      ∀ i, i ≠ i₀ → (inner ℝ (eb i) x : ℝ) = 0 := by
    intro x hx i hi
    -- ⟨eb i, A x⟩ = μ ⟨eb i, x⟩
    have e1 : (inner ℝ (eb i) (Matrix.toEuclideanLin A x) : ℝ)
        = μ * (inner ℝ (eb i) x : ℝ) := by
      rw [hx, inner_smul_right]
    -- ⟨eb i, A x⟩ = ⟨A (eb i), x⟩ = eigenvalues i * ⟨eb i, x⟩
    have e2 : (inner ℝ (eb i) (Matrix.toEuclideanLin A x) : ℝ)
        = hA.eigenvalues i * (inner ℝ (eb i) x : ℝ) := by
      rw [← hsymm (eb i) x, heig i, inner_smul_left]
      simp
    have e3 : (hA.eigenvalues i - μ) * (inner ℝ (eb i) x : ℝ) = 0 := by
      have : hA.eigenvalues i * (inner ℝ (eb i) x : ℝ)
          = μ * (inner ℝ (eb i) x : ℝ) := by rw [← e2, e1]
      nlinarith [this]
    have hne : hA.eigenvalues i - μ ≠ 0 := sub_ne_zero.mpr (hsep i hi)
    exact (mul_eq_zero.mp e3).resolve_left hne
  -- both u and w are scalar multiples of eb i₀
  have hexpand : ∀ (x : EuclideanSpace ℝ (Fin n)),
      Matrix.toEuclideanLin A x = μ • x →
      ∃ t : ℝ, x = t • eb i₀ := by
    intro x hx
    refine ⟨(inner ℝ (eb i₀) x : ℝ), ?_⟩
    have hrepr : ∑ i, (inner ℝ (eb i) x : ℝ) • eb i = x := eb.sum_repr' x
    have hsum : ∑ i, (inner ℝ (eb i) x : ℝ) • eb i
        = (inner ℝ (eb i₀) x : ℝ) • eb i₀ := by
      rw [Finset.sum_eq_single i₀]
      · intro i _ hi
        rw [hclaim x hx i hi, zero_smul]
      · intro h; exact absurd (Finset.mem_univ i₀) h
    rw [hsum] at hrepr
    exact hrepr.symm
  obtain ⟨a, hux⟩ := hexpand u hue
  obtain ⟨c, hwx⟩ := hexpand w hwe
  -- ‖eb i₀‖ = 1
  have heb1 : ‖eb i₀‖ = 1 := eb.orthonormal.1 i₀
  -- |a| = 1, |c| = 1
  have hanorm : |a| = 1 := by
    have : ‖u‖ = |a| * ‖eb i₀‖ := by rw [hux, norm_smul, Real.norm_eq_abs]
    rw [heb1, mul_one] at this
    rw [← this, hu]
  have hcnorm : |c| = 1 := by
    have : ‖w‖ = |c| * ‖eb i₀‖ := by rw [hwx, norm_smul, Real.norm_eq_abs]
    rw [heb1, mul_one] at this
    rw [← this, hw]
  have ha : a = 1 ∨ a = -1 := abs_eq (by norm_num) |>.mp hanorm
  have hc : c = 1 ∨ c = -1 := abs_eq (by norm_num) |>.mp hcnorm
  rcases ha with ha | ha <;> rcases hc with hc | hc
  · left
    rw [hux, hwx, ha, hc]
  · right
    rw [hux, hwx, ha, hc]
    simp
  · right
    rw [hux, hwx, ha, hc]
    simp
  · left
    rw [hux, hwx, ha, hc]

/-- The limiting dual matrix `W∞ = Φ̄∞ᵀ Φ̄∞/n + (δ²/n) Iₙ ∈ ℝ^{n×n}`.  (Since
`bᵀb = I`, the signal term `Φ̄∞ᵀ bᵀ b Φ̄∞/n` collapses to `Φ̄∞ᵀ Φ̄∞/n`.) -/
private def Winf {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf) + (δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- **Operator-norm convergence `W(p) → W∞`.**  Expand
`W(p) = (bΦ+Z)ᵀ(bΦ+Z)/(np)` into signal, cross, and noise blocks and take the four
model limits (`field3_signalLimit`, `field2_decoherence`, `field1_noiseGram`, with
`bᵀb = I`), using continuity of matrix arithmetic and equivalence of norms on
`ℝ^{n×n}` to pass to operator norm. -/
private lemma floor_W_opconv {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) :
    Tendsto
      (fun P : Adm k =>
        opNorm ((1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P)) - Winf M))
      atTop (𝓝 0) := by
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  set A : Adm k → Matrix (Fin k) (Fin n) ℝ :=
    fun P => (1 / Real.sqrt P.1) • (M.Φ P) with hAdef
  set C : Adm k → Matrix (Fin k) (Fin n) ℝ :=
    fun P => (1 / Real.sqrt P.1) • ((M.b P)ᵀ * M.Z P) with hCdef
  set E : Adm k → Matrix (Fin n) (Fin n) ℝ :=
    fun P => (1 / ((n : ℝ) * P.1)) • ((M.Z P)ᵀ * M.Z P) with hEdef
  have hdecomp : ∀ P : Adm k,
      (1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P))
        = (1 / (n : ℝ)) • ((A P)ᵀ * (A P))
          + (1 / (n : ℝ)) • ((A P)ᵀ * (C P))
          + (1 / (n : ℝ)) • ((C P)ᵀ * (A P))
          + E P := by
    intro P
    have hp : (0 : ℝ) < P.1 := by
      have : (0 : ℕ) < P.1 := lt_of_lt_of_le M.hk P.2
      exact_mod_cast this
    have hsq : Real.sqrt P.1 * Real.sqrt P.1 = (P.1 : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hp)
    have hbo : (M.b P)ᵀ * (M.b P) = 1 := M.hb_ortho P
    have hexp : (Ymat M P)ᵀ * (Ymat M P)
        = (M.Φ P)ᵀ * ((M.b P)ᵀ * (M.b P)) * (M.Φ P)
          + (M.Φ P)ᵀ * ((M.b P)ᵀ * M.Z P)
          + (M.Z P)ᵀ * (M.b P) * (M.Φ P)
          + (M.Z P)ᵀ * (M.Z P) := by
      simp only [Ymat, Matrix.transpose_add, Matrix.transpose_mul,
        Matrix.transpose_transpose, Matrix.add_mul, Matrix.mul_add]
      simp only [← Matrix.mul_assoc]
      abel
    rw [hexp, hbo, Matrix.mul_one]
    have hA2 : (1 / (n : ℝ)) • ((A P)ᵀ * (A P))
        = (1 / ((n : ℝ) * P.1)) • ((M.Φ P)ᵀ * (M.Φ P)) := by
      show (1 / (n : ℝ)) • (((1 / Real.sqrt P.1) • (M.Φ P))ᵀ *
          ((1 / Real.sqrt P.1) • (M.Φ P)))
        = (1 / ((n : ℝ) * P.1)) • ((M.Φ P)ᵀ * (M.Φ P))
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
      congr 1
      have hsp : Real.sqrt P.1 ≠ 0 := by positivity
      field_simp
      exact (Real.sq_sqrt (le_of_lt hp)).symm
    have hAC : (1 / (n : ℝ)) • ((A P)ᵀ * (C P))
        = (1 / ((n : ℝ) * P.1)) • ((M.Φ P)ᵀ * ((M.b P)ᵀ * M.Z P)) := by
      show (1 / (n : ℝ)) • (((1 / Real.sqrt P.1) • (M.Φ P))ᵀ *
          ((1 / Real.sqrt P.1) • ((M.b P)ᵀ * M.Z P)))
        = (1 / ((n : ℝ) * P.1)) • ((M.Φ P)ᵀ * ((M.b P)ᵀ * M.Z P))
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
      congr 1
      have hsp : Real.sqrt P.1 ≠ 0 := by positivity
      field_simp
      exact (Real.sq_sqrt (le_of_lt hp)).symm
    have hCA : (1 / (n : ℝ)) • ((C P)ᵀ * (A P))
        = (1 / ((n : ℝ) * P.1)) • (((M.b P)ᵀ * M.Z P)ᵀ * (M.Φ P)) := by
      show (1 / (n : ℝ)) • (((1 / Real.sqrt P.1) • ((M.b P)ᵀ * M.Z P))ᵀ *
          ((1 / Real.sqrt P.1) • (M.Φ P)))
        = (1 / ((n : ℝ) * P.1)) • (((M.b P)ᵀ * M.Z P)ᵀ * (M.Φ P))
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
      congr 1
      have hsp : Real.sqrt P.1 ≠ 0 := by positivity
      field_simp
      exact (Real.sq_sqrt (le_of_lt hp)).symm
    rw [hA2, hAC, hCA]
    show _ = _ + _ + _ + (1 / ((n : ℝ) * P.1)) • ((M.Z P)ᵀ * M.Z P)
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [smul_add]
  have hAlim : Tendsto A atTop (𝓝 M.Φbarinf) := M.field3_signalLimit
  have hClim : Tendsto C atTop (𝓝 0) := M.field2_decoherence
  have hElim : Tendsto E atTop (𝓝 ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ))) :=
    M.field1_noiseGram
  have hmulT : ∀ {r s t : ℕ} {L : Filter (Adm k)}
      {F : Adm k → Matrix (Fin r) (Fin s) ℝ} {G : Adm k → Matrix (Fin r) (Fin t) ℝ}
      {F0 : Matrix (Fin r) (Fin s) ℝ} {G0 : Matrix (Fin r) (Fin t) ℝ},
      Tendsto F L (𝓝 F0) → Tendsto G L (𝓝 G0) →
      Tendsto (fun i => (F i)ᵀ * (G i)) L (𝓝 (F0ᵀ * G0)) := by
    intro r s t L F G F0 G0 hF hG
    have hc : Continuous (fun q : Matrix (Fin r) (Fin s) ℝ × Matrix (Fin r) (Fin t) ℝ =>
        q.1ᵀ * q.2) :=
      (continuous_fst.matrix_transpose).matrix_mul continuous_snd
    have := (hc.tendsto (F0, G0)).comp (hF.prodMk_nhds hG)
    exact this
  have hAAlim : Tendsto (fun P : Adm k => (1 / (n : ℝ)) • ((A P)ᵀ * (A P)))
      atTop (𝓝 ((1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf))) := by
    have hmul : Tendsto (fun P : Adm k => (A P)ᵀ * (A P)) atTop
        (𝓝 (M.Φbarinfᵀ * M.Φbarinf)) := hmulT hAlim hAlim
    have h := hmul.const_smul (1 / (n : ℝ))
    exact h
  have hAClim : Tendsto (fun P : Adm k => (1 / (n : ℝ)) • ((A P)ᵀ * (C P)))
      atTop (𝓝 (0 : Matrix (Fin n) (Fin n) ℝ)) := by
    have hmul : Tendsto (fun P : Adm k => (A P)ᵀ * (C P)) atTop
        (𝓝 (M.Φbarinfᵀ * (0 : Matrix (Fin k) (Fin n) ℝ))) := hmulT hAlim hClim
    have h := hmul.const_smul (1 / (n : ℝ))
    simpa using h
  have hCAlim : Tendsto (fun P : Adm k => (1 / (n : ℝ)) • ((C P)ᵀ * (A P)))
      atTop (𝓝 (0 : Matrix (Fin n) (Fin n) ℝ)) := by
    have hmul : Tendsto (fun P : Adm k => (C P)ᵀ * (A P)) atTop
        (𝓝 ((0 : Matrix (Fin k) (Fin n) ℝ)ᵀ * M.Φbarinf)) := hmulT hClim hAlim
    have h := hmul.const_smul (1 / (n : ℝ))
    simpa using h
  have hRHS : Tendsto
      (fun P : Adm k =>
        (1 / (n : ℝ)) • ((A P)ᵀ * (A P))
          + (1 / (n : ℝ)) • ((A P)ᵀ * (C P))
          + (1 / (n : ℝ)) • ((C P)ᵀ * (A P))
          + E P)
      atTop (𝓝 (Winf M)) := by
    have := ((hAAlim.add hAClim).add hCAlim).add hElim
    simpa only [add_zero, Winf] using this
  have hWlim : Tendsto
      (fun P : Adm k => (1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P)))
      atTop (𝓝 (Winf M)) := by
    refine hRHS.congr ?_
    intro P; exact (hdecomp P).symm
  have hDlim : Tendsto
      (fun P : Adm k => (1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P)) - Winf M)
      atTop (𝓝 (0 : Matrix (Fin n) (Fin n) ℝ)) := by
    have := hWlim.sub (tendsto_const_nhds (x := Winf M))
    simpa using this
  have hcont : Continuous (opNorm (m := n)) := by
    have hlin : Continuous
        (fun A : Matrix (Fin n) (Fin n) ℝ =>
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A :
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) := by
      have hc : Continuous
          ((Matrix.toEuclideanCLM (𝕜 := ℝ)).toAlgEquiv.toLinearMap :
              Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
                (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
        LinearMap.continuous_of_finiteDimensional _
      exact hc
    have : (opNorm (m := n)) =
        fun A : Matrix (Fin n) (Fin n) ℝ =>
          ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A :
            EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))‖ := rfl
    rw [this]
    exact hlin.norm
  have h0 : opNorm (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
    rw [opNorm, map_zero, norm_zero]
  have hfin := (hcont.tendsto 0).comp hDlim
  rw [h0] at hfin
  exact hfin

/-- `W∞ = Φ̄∞ᵀΦ̄∞/n + (δ²/n)I` is Hermitian (symmetric, real). -/
private lemma winf_hermitian {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) :
    (Winf M).IsHermitian := by
  unfold Winf
  have hA : (M.Φbarinfᵀ * M.Φbarinf).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self M.Φbarinf
  have h1 : ((1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul]
    simp only [star_trivial]
    rw [hA]
  have h2 : ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul]
    simp only [star_trivial]
    rw [Matrix.isHermitian_one]
  exact h1.add h2

/-- **Signal eigenpair of `W∞`.**  For each `i`, the vector `p_i := Φ̄∞ᵀ νn i`
is a nonzero eigenvector of `W∞` at eigenvalue `λ i + δ²/n`. -/
private lemma winf_signal_eigenpair {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (i : Fin k) :
    Matrix.toEuclideanLin (Winf M) (Matrix.toEuclideanLin M.Φbarinfᵀ (M.νn i))
      = (M.lam i + δ2 / n) • (Matrix.toEuclideanLin M.Φbarinfᵀ (M.νn i)) ∧
    Matrix.toEuclideanLin M.Φbarinfᵀ (M.νn i) ≠ 0 := by
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn
  set v := M.νn i with hvdef
  set pv := Matrix.toEuclideanLin M.Φbarinfᵀ v with hpvdef
  have heig1 : Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinf * M.Φbarinfᵀ)) v
      = M.lam i • v := M.hνn_eig i
  have hsmul1 : Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinf * M.Φbarinfᵀ)) v
      = (1 / (n : ℝ)) • Matrix.toEuclideanLin (M.Φbarinf * M.Φbarinfᵀ) v := by
    rw [map_smul]; rfl
  have heig2 : Matrix.toEuclideanLin (M.Φbarinf * M.Φbarinfᵀ) v = (n : ℝ) • (M.lam i • v) := by
    have hb : (1 / (n : ℝ)) • Matrix.toEuclideanLin (M.Φbarinf * M.Φbarinfᵀ) v
        = M.lam i • v := by rw [← hsmul1]; exact heig1
    have h2 := congrArg (fun x => (n : ℝ) • x) hb
    simp only at h2
    rw [smul_smul, mul_one_div, div_self hnne, one_smul] at h2
    rw [h2]
  refine ⟨?_, ?_⟩
  · unfold Winf
    rw [map_add, LinearMap.add_apply]
    have hmap_smul_one :
        Matrix.toEuclideanLin ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) pv
          = (δ2 / n) • pv := by
      rw [map_smul]
      simp [Matrix.toEuclideanLin_apply, Matrix.one_mulVec]
    have hmap1 :
        Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf)) pv
          = M.lam i • pv := by
      rw [hpvdef, map_smul, LinearMap.smul_apply, toEuclideanLin_comp]
      rw [show M.Φbarinfᵀ * M.Φbarinf * M.Φbarinfᵀ
            = M.Φbarinfᵀ * (M.Φbarinf * M.Φbarinfᵀ) from by rw [Matrix.mul_assoc]]
      rw [← toEuclideanLin_comp, heig2]
      rw [map_smul, map_smul]
      rw [smul_smul, smul_comm, one_div, inv_mul_cancel₀ hnne, one_smul]
    rw [hmap1, hmap_smul_one]
    rw [add_smul]
  · have hnorm : ‖pv‖ ^ 2
        = (inner ℝ v (Matrix.toEuclideanLin ((M.Φbarinfᵀ)ᵀ * M.Φbarinfᵀ) v) : ℝ) := by
      rw [hpvdef]; exact normSq_toEuclideanLin M.Φbarinfᵀ v
    rw [Matrix.transpose_transpose] at hnorm
    rw [heig2] at hnorm
    rw [inner_smul_right] at hnorm
    have hunit : (inner ℝ v v : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, hvdef, M.hνn_unit i]; norm_num
    rw [inner_smul_right, hunit] at hnorm
    have hpos : (0 : ℝ) < ‖pv‖ ^ 2 := by
      rw [hnorm]
      have := M.hlam_pos i
      positivity
    intro hzero
    rw [hzero] at hpos
    simp at hpos

/-- The eigenvectors `νn` of `N^{(n)} = Φ̄∞ Φ̄∞ᵀ/n` are pairwise orthogonal
(distinct eigenvalues `lam`). -/
private lemma winf_nn_ortho {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    {i i' : Fin k} (hii : i ≠ i') :
    (inner ℝ (M.νn i) (M.νn i') : ℝ) = 0 := by
  set Nn := (1 / (n : ℝ)) • (M.Φbarinf * M.Φbarinfᵀ) with hNndef
  have hsymm : (Matrix.toEuclideanLin Nn).IsSymmetric := by
    apply (Matrix.isHermitian_iff_isSymmetric).mp
    rw [hNndef]
    have hA : (M.Φbarinf * M.Φbarinfᵀ).IsHermitian :=
      Matrix.isHermitian_mul_conjTranspose_self M.Φbarinf
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul]
    simp only [star_trivial]
    rw [hA]
  have e1 : (inner ℝ (M.νn i) (Matrix.toEuclideanLin Nn (M.νn i')) : ℝ)
      = M.lam i' * (inner ℝ (M.νn i) (M.νn i') : ℝ) := by
    rw [M.hνn_eig i', inner_smul_right]
  have e2 : (inner ℝ (M.νn i) (Matrix.toEuclideanLin Nn (M.νn i')) : ℝ)
      = M.lam i * (inner ℝ (M.νn i) (M.νn i') : ℝ) := by
    rw [← hsymm (M.νn i) (M.νn i'), M.hνn_eig i, inner_smul_left]
    simp
  have e3 : (M.lam i - M.lam i') * (inner ℝ (M.νn i) (M.νn i') : ℝ) = 0 := by
    have hh : M.lam i * (inner ℝ (M.νn i) (M.νn i') : ℝ)
        = M.lam i' * (inner ℝ (M.νn i) (M.νn i') : ℝ) := by rw [← e2, e1]
    nlinarith [hh]
  have hne : M.lam i - M.lam i' ≠ 0 :=
    sub_ne_zero.mpr (fun h => hii (M.hlam_sorted.injective h))
  exact (mul_eq_zero.mp e3).resolve_left hne

/-- `νn` forms an orthonormal family in `ℝ^k`. -/
private lemma winf_nn_orthonormal {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) :
    Orthonormal ℝ M.νn := by
  rw [orthonormal_iff_ite]
  intro i i'
  by_cases h : i = i'
  · subst h
    rw [if_pos rfl, real_inner_self_eq_norm_sq, M.hνn_unit i]; norm_num
  · rw [if_neg h]
    exact winf_nn_ortho M h

/-- `νn` as an orthonormal basis of `ℝ^k`. -/
private def winf_nn_basis {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) :
    OrthonormalBasis (Fin k) ℝ (EuclideanSpace ℝ (Fin k)) :=
  haveI : Nonempty (Fin k) := ⟨⟨0, M.hk⟩⟩
  (basisOfOrthonormalOfCardEqFinrank (winf_nn_orthonormal M)
    (by simp)).toOrthonormalBasis (by
      rw [coe_basisOfOrthonormalOfCardEqFinrank]
      exact winf_nn_orthonormal M)

private lemma winf_nn_basis_apply {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) (i : Fin k) :
    winf_nn_basis M i = M.νn i := by
  haveI : Nonempty (Fin k) := ⟨⟨0, M.hk⟩⟩
  have h : (winf_nn_basis M : Fin k → EuclideanSpace ℝ (Fin k)) = M.νn := by
    unfold winf_nn_basis
    rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  exact congrFun h i

/-- **Key parallelism.**  Any vector `v` with `W∞ v = (λⱼ+δ²/n) v` is a scalar
multiple of `pvⱼ := Φ̄∞ᵀ νn j`. -/
private lemma winf_key_parallel {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (j : Fin k) (v : EuclideanSpace ℝ (Fin n))
    (hv : Matrix.toEuclideanLin (Winf M) v = (M.lam j + δ2 / n) • v) :
    ∃ c : ℝ, v = c • Matrix.toEuclideanLin M.Φbarinfᵀ (M.νn j) := by
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn
  have hlamj := M.hlam_pos j
  have hnlam : (n : ℝ) * M.lam j ≠ 0 := by positivity
  -- Step A: (1/n)•(Φᵀ Φ) v = lam j • v
  have hstepA : Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf)) v
      = M.lam j • v := by
    have hexp : Matrix.toEuclideanLin (Winf M) v
        = Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf)) v
          + (δ2 / n) • v := by
      unfold Winf
      rw [map_add, LinearMap.add_apply]
      congr 1
      rw [map_smul]
      simp [Matrix.toEuclideanLin_apply, Matrix.one_mulVec]
    rw [hexp, add_smul] at hv
    exact add_right_cancel hv
  -- Rewrite: toEuclideanLin (Φᵀ Φ) v = (n lam j) • v
  have hPhiPhi : Matrix.toEuclideanLin (M.Φbarinfᵀ * M.Φbarinf) v = ((n : ℝ) * M.lam j) • v := by
    have hs : (1 / (n : ℝ)) • Matrix.toEuclideanLin (M.Φbarinfᵀ * M.Φbarinf) v
        = M.lam j • v := by
      have hmap : Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf)) v
          = (1 / (n : ℝ)) • Matrix.toEuclideanLin (M.Φbarinfᵀ * M.Φbarinf) v := by
        rw [map_smul]; rfl
      rw [← hmap]; exact hstepA
    have := congrArg (fun x => (n : ℝ) • x) hs
    simp only at this
    rw [smul_smul, mul_one_div, div_self hnne, one_smul, smul_smul] at this
    exact this
  -- y := Φbarinf v
  set y := Matrix.toEuclideanLin M.Φbarinf v with hydef
  -- Step B: Nn y = lam j • y
  have hstepB : Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinf * M.Φbarinfᵀ)) y
      = M.lam j • y := by
    have hmap : Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinf * M.Φbarinfᵀ)) y
        = (1 / (n : ℝ)) • Matrix.toEuclideanLin (M.Φbarinf * M.Φbarinfᵀ) y := by
      rw [map_smul]; rfl
    rw [hmap]
    have hcomp : Matrix.toEuclideanLin (M.Φbarinf * M.Φbarinfᵀ) y
        = ((n : ℝ) * M.lam j) • y := by
      rw [hydef, toEuclideanLin_comp]
      rw [show M.Φbarinf * M.Φbarinfᵀ * M.Φbarinf
            = M.Φbarinf * (M.Φbarinfᵀ * M.Φbarinf) from by rw [Matrix.mul_assoc]]
      rw [← toEuclideanLin_comp, hPhiPhi, map_smul]
    rw [hcomp, smul_smul]
    congr 1
    field_simp
  -- Step C: y = c • νn j.  Expand y in the νn orthonormal basis.
  have hkill : ∀ i : Fin k, i ≠ j → (inner ℝ (M.νn i) y : ℝ) = 0 := by
    intro i hi
    set Nn := (1 / (n : ℝ)) • (M.Φbarinf * M.Φbarinfᵀ) with hNndef
    have hsymm : (Matrix.toEuclideanLin Nn).IsSymmetric := by
      apply (Matrix.isHermitian_iff_isSymmetric).mp
      rw [hNndef]
      have hA : (M.Φbarinf * M.Φbarinfᵀ).IsHermitian :=
        Matrix.isHermitian_mul_conjTranspose_self M.Φbarinf
      unfold Matrix.IsHermitian
      rw [Matrix.conjTranspose_smul]
      simp only [star_trivial]
      rw [hA]
    have e1 : (inner ℝ (M.νn i) (Matrix.toEuclideanLin Nn y) : ℝ)
        = M.lam j * (inner ℝ (M.νn i) y : ℝ) := by
      rw [hNndef, hstepB, inner_smul_right]
    have e2 : (inner ℝ (M.νn i) (Matrix.toEuclideanLin Nn y) : ℝ)
        = M.lam i * (inner ℝ (M.νn i) y : ℝ) := by
      rw [← hsymm (M.νn i) y, M.hνn_eig i, inner_smul_left]; simp
    have e3 : (M.lam i - M.lam j) * (inner ℝ (M.νn i) y : ℝ) = 0 := by
      have hh : M.lam i * (inner ℝ (M.νn i) y : ℝ)
          = M.lam j * (inner ℝ (M.νn i) y : ℝ) := by rw [← e2, e1]
      nlinarith [hh]
    have hne : M.lam i - M.lam j ≠ 0 :=
      sub_ne_zero.mpr (fun h => hi (M.hlam_sorted.injective h))
    exact (mul_eq_zero.mp e3).resolve_left hne
  have hyc : y = (inner ℝ (M.νn j) y : ℝ) • M.νn j := by
    have hrepr : ∑ i, (inner ℝ (winf_nn_basis M i) y : ℝ) • winf_nn_basis M i = y :=
      (winf_nn_basis M).sum_repr' y
    have hrepr' : ∑ i, (inner ℝ (M.νn i) y : ℝ) • M.νn i = y := by
      have hcong : (∑ i, (inner ℝ (M.νn i) y : ℝ) • M.νn i)
          = ∑ i, (inner ℝ (winf_nn_basis M i) y : ℝ) • winf_nn_basis M i :=
        Finset.sum_congr rfl (fun i _ => by rw [winf_nn_basis_apply])
      rw [hcong, hrepr]
    rw [Finset.sum_eq_single j
        (fun i _ hi => by rw [hkill i hi, zero_smul])
        (fun h => absurd (Finset.mem_univ j) h)] at hrepr'
    exact hrepr'.symm
  set c := (inner ℝ (M.νn j) y : ℝ) with hcdef
  -- Step D: v = (c/(n lam j)) • pv
  refine ⟨c / ((n : ℝ) * M.lam j), ?_⟩
  have hvrec : v = (1 / ((n : ℝ) * M.lam j)) • Matrix.toEuclideanLin M.Φbarinfᵀ y := by
    rw [hydef, toEuclideanLin_comp, hPhiPhi, smul_smul,
      one_div, inv_mul_cancel₀ hnlam, one_smul]
  rw [hvrec, hyc, map_smul, smul_smul]
  congr 1
  rw [hcdef]
  field_simp

/-- **Simple multiplicity.**  As a Hermitian matrix, the eigenvalue `λ j + δ²/n`
of `W∞` is attained by exactly one Mathlib eigenvalue index. -/
private lemma winf_eigenvalue_multiplicity {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (j : Fin k) :
    (Finset.univ.filter
        (fun i : Fin n => (winf_hermitian M).eigenvalues i = M.lam j + δ2 / n)).card
      = 1 := by
  classical
  set hA := winf_hermitian M with hAdef
  set μ : ℝ := M.lam j + δ2 / n with hμdef
  set eb := hA.eigenvectorBasis with hebdef
  set pv := Matrix.toEuclideanLin M.Φbarinfᵀ (M.νn j) with hpvdef
  have heig : ∀ i, Matrix.toEuclideanLin (Winf M) (eb i) = hA.eigenvalues i • (eb i) := by
    intro i
    have h1 : Matrix.toEuclideanLin (Winf M) (eb i)
        = WithLp.toLp 2 ((Winf M) *ᵥ WithLp.ofLp (eb i)) :=
      Matrix.toEuclideanLin_apply (Winf M) (eb i)
    rw [h1]
    rw [hAdef, hebdef, hA.mulVec_eigenvectorBasis i]
    rfl
  obtain ⟨hpv_eig, hpv_ne⟩ := winf_signal_eigenpair M j
  have hpv_eig' : Matrix.toEuclideanLin (Winf M) pv = μ • pv := by
    rw [hpvdef, hμdef]; exact hpv_eig
  have hpvnorm_pos : (0 : ℝ) < ‖pv‖ ^ 2 := by
    have : ‖pv‖ ≠ 0 := norm_ne_zero_iff.mpr hpv_ne
    positivity
  set F := Finset.univ.filter (fun i : Fin n => hA.eigenvalues i = μ) with hFdef
  have hebc : ∀ i ∈ F, ∃ c : ℝ, c ≠ 0 ∧ eb i = c • pv := by
    intro i hi
    rw [hFdef, Finset.mem_filter] at hi
    have hieq : hA.eigenvalues i = μ := hi.2
    have heigi : Matrix.toEuclideanLin (Winf M) (eb i) = μ • (eb i) := by
      rw [heig i, hieq]
    obtain ⟨c, hc⟩ := winf_key_parallel M j (eb i) heigi
    refine ⟨c, ?_, hc⟩
    intro hc0
    have hz : eb i = 0 := by rw [hc, hc0, zero_smul]
    have hu : ‖eb i‖ = 1 := eb.orthonormal.1 i
    rw [hz, norm_zero] at hu; norm_num at hu
  -- card ≤ 1
  have hle : F.card ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨i₁, hi₁, i₂, hi₂, hne⟩ := Finset.one_lt_card.mp h
    obtain ⟨c₁, hc₁ne, hc₁⟩ := hebc i₁ hi₁
    obtain ⟨c₂, hc₂ne, hc₂⟩ := hebc i₂ hi₂
    have horth : (inner ℝ (eb i₁) (eb i₂) : ℝ) = 0 := by
      have := eb.orthonormal.2 hne
      simpa using this
    have hval : (inner ℝ (eb i₁) (eb i₂) : ℝ) = c₁ * c₂ * ‖pv‖ ^ 2 := by
      rw [hc₁, hc₂, inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
      simp [mul_assoc]
    rw [hval] at horth
    have hne0 : c₁ * c₂ * ‖pv‖ ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hc₁ne hc₂ne) (ne_of_gt hpvnorm_pos)
    exact hne0 horth
  -- card ≥ 1
  have hge : 1 ≤ F.card := by
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
    intro hempty
    have hkill : ∀ i : Fin n, (inner ℝ (eb i) pv : ℝ) = 0 := by
      intro i
      have hine : hA.eigenvalues i ≠ μ := by
        intro he
        have : i ∈ F := by rw [hFdef, Finset.mem_filter]; exact ⟨Finset.mem_univ i, he⟩
        rw [hempty] at this; exact absurd this (Finset.notMem_empty i)
      have hsymm : (Matrix.toEuclideanLin (Winf M)).IsSymmetric :=
        (Matrix.isHermitian_iff_isSymmetric).mp hA
      have e1 : (inner ℝ (eb i) (Matrix.toEuclideanLin (Winf M) pv) : ℝ)
          = μ * (inner ℝ (eb i) pv : ℝ) := by
        rw [hpv_eig', inner_smul_right]
      have e2 : (inner ℝ (eb i) (Matrix.toEuclideanLin (Winf M) pv) : ℝ)
          = hA.eigenvalues i * (inner ℝ (eb i) pv : ℝ) := by
        rw [← hsymm (eb i) pv, heig i, inner_smul_left]; simp
      have e3 : (hA.eigenvalues i - μ) * (inner ℝ (eb i) pv : ℝ) = 0 := by
        have hh : hA.eigenvalues i * (inner ℝ (eb i) pv : ℝ)
            = μ * (inner ℝ (eb i) pv : ℝ) := by rw [← e2, e1]
        nlinarith [hh]
      exact (mul_eq_zero.mp e3).resolve_left (sub_ne_zero.mpr hine)
    have hpvzero : pv = 0 := by
      have hrepr : ∑ i, (inner ℝ (eb i) pv : ℝ) • eb i = pv := eb.sum_repr' pv
      rw [← hrepr]
      apply Finset.sum_eq_zero
      intro i _
      rw [hkill i, zero_smul]
    exact hpv_ne hpvzero
  omega

/-- **Exhaustion.** Every eigenvalue of `W∞` that is not the bulk value `δ²/n`
equals `λⱼ + δ²/n` for some signal index `j`. -/
private lemma winf_eigenvalue_exhaust {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) :
    ∀ i : Fin n, (winf_hermitian M).eigenvalues i ≠ δ2 / n →
      ∃ j : Fin k, (winf_hermitian M).eigenvalues i = M.lam j + δ2 / n := by
  classical
  set hA := winf_hermitian M with hAdef
  set μ : ℝ := δ2 / n with hμdef
  set eb := hA.eigenvectorBasis with hebdef
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn
  have heig : ∀ i, Matrix.toEuclideanLin (Winf M) (eb i) = hA.eigenvalues i • (eb i) := by
    intro i
    have h1 : Matrix.toEuclideanLin (Winf M) (eb i)
        = WithLp.toLp 2 ((Winf M) *ᵥ WithLp.ofLp (eb i)) :=
      Matrix.toEuclideanLin_apply (Winf M) (eb i)
    rw [h1, hAdef, hebdef, hA.mulVec_eigenvectorBasis i]
    rfl
  set Nn := (1 / (n : ℝ)) • (M.Φbarinf * M.Φbarinfᵀ) with hNndef
  have hNnsymm : (Matrix.toEuclideanLin Nn).IsSymmetric := by
    apply (Matrix.isHermitian_iff_isSymmetric).mp
    rw [hNndef]
    have hAh : (M.Φbarinf * M.Φbarinfᵀ).IsHermitian :=
      Matrix.isHermitian_mul_conjTranspose_self M.Φbarinf
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul]
    simp only [star_trivial]
    rw [hAh]
  intro i hine
  set c := hA.eigenvalues i with hcdef
  have hci : Matrix.toEuclideanLin (Winf M) (eb i) = c • eb i := heig i
  have hB : Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf)) (eb i)
      = (c - μ) • eb i := by
    have hexp : Matrix.toEuclideanLin (Winf M) (eb i)
        = Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf)) (eb i)
          + μ • eb i := by
      unfold Winf
      rw [map_add, LinearMap.add_apply]
      congr 1
      rw [hμdef, map_smul]
      simp [Matrix.toEuclideanLin_apply, Matrix.one_mulVec]
    rw [hexp] at hci
    have hcancel := add_right_cancel (a := Matrix.toEuclideanLin
      ((1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf)) (eb i)) (b := μ • eb i)
      (c := (c - μ) • eb i)
    apply hcancel
    rw [hci, ← add_smul]
    congr 1
    ring
  have hPhiPhi : Matrix.toEuclideanLin (M.Φbarinfᵀ * M.Φbarinf) (eb i)
      = ((n : ℝ) * (c - μ)) • eb i := by
    have hmap : Matrix.toEuclideanLin ((1 / (n : ℝ)) • (M.Φbarinfᵀ * M.Φbarinf)) (eb i)
        = (1 / (n : ℝ)) • Matrix.toEuclideanLin (M.Φbarinfᵀ * M.Φbarinf) (eb i) := by
      rw [map_smul]; rfl
    rw [hmap] at hB
    have hscaled := congrArg (fun x => (n : ℝ) • x) hB
    simp only at hscaled
    rw [smul_smul, mul_one_div, div_self hnne, one_smul, smul_smul] at hscaled
    rw [hscaled]
  set y := Matrix.toEuclideanLin M.Φbarinf (eb i) with hydef
  have hNny : Matrix.toEuclideanLin Nn y = (c - μ) • y := by
    rw [hNndef, map_smul]
    have hcomp : Matrix.toEuclideanLin (M.Φbarinf * M.Φbarinfᵀ) y
        = ((n : ℝ) * (c - μ)) • y := by
      rw [hydef, toEuclideanLin_comp]
      rw [show M.Φbarinf * M.Φbarinfᵀ * M.Φbarinf
            = M.Φbarinf * (M.Φbarinfᵀ * M.Φbarinf) from by rw [Matrix.mul_assoc]]
      rw [← toEuclideanLin_comp, hPhiPhi, map_smul]
    show (1 / (n : ℝ)) • Matrix.toEuclideanLin (M.Φbarinf * M.Φbarinfᵀ) y = _
    rw [hcomp, smul_smul]
    congr 1
    field_simp
  have hcμ : c - μ ≠ 0 := sub_ne_zero.mpr hine
  have hy_ne : y ≠ 0 := by
    intro hy0
    have hzero : Matrix.toEuclideanLin (M.Φbarinfᵀ * M.Φbarinf) (eb i) = 0 := by
      rw [← toEuclideanLin_comp, ← hydef, hy0, map_zero]
    rw [hPhiPhi] at hzero
    have hebne : eb i ≠ 0 := by
      intro h; have hu := eb.orthonormal.1 i; rw [h, norm_zero] at hu; norm_num at hu
    have hscal : (n : ℝ) * (c - μ) ≠ 0 := mul_ne_zero hnne hcμ
    exact hebne (by
      rcases smul_eq_zero.mp hzero with h | h
      · exact absurd h hscal
      · exact h)
  have hkill : ∀ i' : Fin k, M.lam i' ≠ c - μ → (inner ℝ (M.νn i') y : ℝ) = 0 := by
    intro i' hi'
    have e1 : (inner ℝ (M.νn i') (Matrix.toEuclideanLin Nn y) : ℝ)
        = (c - μ) * (inner ℝ (M.νn i') y : ℝ) := by
      rw [hNny, inner_smul_right]
    have e2 : (inner ℝ (M.νn i') (Matrix.toEuclideanLin Nn y) : ℝ)
        = M.lam i' * (inner ℝ (M.νn i') y : ℝ) := by
      rw [← hNnsymm (M.νn i') y]
      have heq : Matrix.toEuclideanLin Nn (M.νn i') = M.lam i' • M.νn i' := M.hνn_eig i'
      rw [heq, inner_smul_left]; simp
    have e3 : (M.lam i' - (c - μ)) * (inner ℝ (M.νn i') y : ℝ) = 0 := by
      have hh : M.lam i' * (inner ℝ (M.νn i') y : ℝ)
          = (c - μ) * (inner ℝ (M.νn i') y : ℝ) := by rw [← e2, e1]
      nlinarith [hh]
    exact (mul_eq_zero.mp e3).resolve_left (sub_ne_zero.mpr hi')
  by_contra hno
  push_neg at hno
  have hyzero : y = 0 := by
    have hrepr : ∑ i', (inner ℝ (winf_nn_basis M i') y : ℝ) • winf_nn_basis M i' = y :=
      (winf_nn_basis M).sum_repr' y
    rw [← hrepr]
    apply Finset.sum_eq_zero
    intro i' _
    rw [winf_nn_basis_apply]
    rw [hkill i' (fun h => hno i' (by linarith [h]))]
    rw [zero_smul]
  exact hy_ne hyzero

/-- **Bulk multiplicity.**  The eigenvalue `δ²/n` of `W∞` is attained by exactly
`n − k` Mathlib eigenvalue indices.  Equivalently, the `δ²/n`-eigenspace of
`W∞` — which is the kernel of `A := (1/n) Φ̄∞ᵀΦ̄∞ = W∞ − (δ²/n)·I` — has
dimension `n − k`, since `rank A = rank Φ̄∞ = k`. -/
private lemma winf_bulk_multiplicity {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) :
    (Finset.univ.filter
        (fun i : Fin n => (winf_hermitian M).eigenvalues i = δ2 / n)).card
      = n - k := by
  classical
  set hA := winf_hermitian M with hAdef
  set μ : ℝ := δ2 / n with hμdef
  set eb := hA.eigenvectorBasis with hebdef
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn
  have heig : ∀ i, Matrix.toEuclideanLin (Winf M) (eb i) = hA.eigenvalues i • (eb i) := by
    intro i
    have h1 : Matrix.toEuclideanLin (Winf M) (eb i)
        = WithLp.toLp 2 ((Winf M) *ᵥ WithLp.ofLp (eb i)) :=
      Matrix.toEuclideanLin_apply (Winf M) (eb i)
    rw [h1, hAdef, hebdef, hA.mulVec_eigenvectorBasis i]
    rfl
  set Nn := (1 / (n : ℝ)) • (M.Φbarinf * M.Φbarinfᵀ) with hNndef
  have hNnsymm : (Matrix.toEuclideanLin Nn).IsSymmetric := by
    apply (Matrix.isHermitian_iff_isSymmetric).mp
    rw [hNndef]
    have hAh : (M.Φbarinf * M.Φbarinfᵀ).IsHermitian :=
      Matrix.isHermitian_mul_conjTranspose_self M.Φbarinf
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul]
    simp only [star_trivial]
    rw [hAh]
  have hexhaust : ∀ i : Fin n, hA.eigenvalues i ≠ μ →
      ∃ j : Fin k, hA.eigenvalues i = M.lam j + μ := winf_eigenvalue_exhaust M
  set S := Finset.univ.filter (fun i : Fin n => hA.eigenvalues i = μ) with hSdef
  set T : Fin k → Finset (Fin n) :=
    fun j => Finset.univ.filter (fun i : Fin n => hA.eigenvalues i = M.lam j + μ) with hTdef
  have hTcard : ∀ j, (T j).card = 1 := by
    intro j
    rw [hTdef]
    have hmul := winf_eigenvalue_multiplicity M j
    rw [hAdef, hμdef]
    exact hmul
  have hTdisj : (Finset.univ : Finset (Fin k)).toSet.PairwiseDisjoint T := by
    intro j _ j' _ hjj'
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    rw [hTdef, Finset.mem_filter] at hi hi'
    have heqv : M.lam j + μ = M.lam j' + μ := by rw [← hi.2, hi'.2]
    have hlam : M.lam j = M.lam j' := by linarith
    exact hjj' (M.hlam_sorted.injective hlam)
  have hTmem : ∀ (j : Fin k) (i : Fin n),
      i ∈ T j ↔ hA.eigenvalues i = M.lam j + μ := by
    intro j i
    rw [hTdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hcompl : Finset.univ.filter (fun i : Fin n => hA.eigenvalues i ≠ μ)
      = Finset.univ.biUnion T := by
    ext i
    rw [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · intro hine
      obtain ⟨j, hj⟩ := hexhaust i hine.2
      exact ⟨j, Finset.mem_univ j, (hTmem j i).mpr hj⟩
    · rintro ⟨j, _, hj⟩
      rw [hTmem j i] at hj
      refine ⟨Finset.mem_univ i, ?_⟩
      rw [hj]
      have hlam := M.hlam_pos j
      intro h; linarith [h]
  have hcomplcard : (Finset.univ.filter (fun i : Fin n => hA.eigenvalues i ≠ μ)).card = k := by
    rw [hcompl, Finset.card_biUnion hTdisj]
    simp only [hTcard]
    simp
  have hsplit : S.card + (Finset.univ.filter (fun i : Fin n => hA.eigenvalues i ≠ μ)).card
      = Fintype.card (Fin n) := by
    rw [hSdef]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  rw [Fintype.card_fin] at hsplit
  rw [hcomplcard] at hsplit
  have hScard : S.card = n - k := by omega
  exact hScard

/-- Exhaustion: every eigenvalue of `W∞` is either `δ²/n` (bulk) or `λⱼ+δ²/n`
(a signal value).  So if `c ≠ δ²/n` and `c ≠ λⱼ+δ²/n` for all `j`, then `c` is
not an eigenvalue of `W∞`. -/
private lemma winf_eigenvalue_not_c {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (c : ℝ) (hcbulk : ¬ c = δ2 / n)
    (hcsig : ∀ j : Fin k, c ≠ M.lam j + δ2 / n) :
    ∀ i : Fin n, (winf_hermitian M).eigenvalues i ≠ c := by
  intro i hi
  rcases eq_or_ne ((winf_hermitian M).eigenvalues i) (δ2 / n) with hb | hb
  · exact hcbulk (by rw [← hi, hb])
  · obtain ⟨j, hj⟩ := winf_eigenvalue_exhaust M i hb
    exact hcsig j (by rw [← hi, hj])

/-- The multiset of `W∞` eigenvalues (Mathlib enumeration) is
`{λ i + δ²/n : i} + (n−k)·{δ²/n}`. -/
private lemma winf_eigenvalues_multiset {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) :
    Multiset.map (winf_hermitian M).eigenvalues Finset.univ.val
      = Multiset.map (fun i : Fin k => M.lam i + δ2 / n) Finset.univ.val
        + Multiset.replicate (n - k) (δ2 / n) := by
  classical
  set hA := winf_hermitian M with hAdef
  set μ : ℝ := δ2 / n with hμdef
  set g : Fin k → ℝ := fun i => M.lam i + δ2 / n with hgdef
  have hlampos : ∀ i, 0 < M.lam i := M.hlam_pos
  have hginj : Function.Injective g := by
    intro a b hab
    rw [hgdef] at hab
    simp only at hab
    exact M.hlam_sorted.injective (by linarith [hab])
  have hgne : ∀ i, g i ≠ μ := by
    intro i h
    rw [hgdef, hμdef] at h
    simp only at h
    have := hlampos i; linarith
  apply Multiset.ext.mpr
  intro c
  rw [Multiset.count_map]
  rw [Multiset.count_add, Multiset.count_map, Multiset.count_replicate]
  by_cases hcbulk : c = μ
  · subst hcbulk
    have hkfilter : (Finset.univ.filter (fun a : Fin k => μ = g a)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro a _; exact fun h => (hgne a) h.symm
    rw [show (Multiset.filter (fun a => μ = g a) Finset.univ.val).card
          = (Finset.univ.filter (fun a : Fin k => μ = g a)).card from rfl,
       hkfilter, Finset.card_empty]
    rw [if_pos rfl]
    have hbulk := winf_bulk_multiplicity M
    have hconv : (Multiset.filter (fun a => μ = hA.eigenvalues a) Finset.univ.val).card
          = (Finset.univ.filter (fun i : Fin n => hA.eigenvalues i = μ)).card := by
      have hfe : (Finset.univ.filter (fun i : Fin n => μ = hA.eigenvalues i))
            = (Finset.univ.filter (fun i : Fin n => hA.eigenvalues i = μ)) := by
        apply Finset.filter_congr; intro x _; exact eq_comm
      rw [show (Multiset.filter (fun a => μ = hA.eigenvalues a) Finset.univ.val).card
            = (Finset.univ.filter (fun i : Fin n => μ = hA.eigenvalues i)).card from rfl, hfe]
    rw [hconv, hbulk]; ring
  · by_cases hcsig : ∃ j, c = g j
    · obtain ⟨j, hj⟩ := hcsig
      subst hj
      rw [if_neg (fun h => hgne j h.symm)]
      have hsigcount : (Multiset.filter (fun a => g j = g a) Finset.univ.val).card = 1 := by
        rw [show (Multiset.filter (fun a => g j = g a) Finset.univ.val).card
              = (Finset.univ.filter (fun a : Fin k => g j = g a)).card from rfl]
        rw [show (Finset.univ.filter (fun a : Fin k => g j = g a))
              = {j} from by
                apply Finset.eq_singleton_iff_unique_mem.mpr
                refine ⟨by simp, ?_⟩
                intro x hx
                rw [Finset.mem_filter] at hx
                exact (hginj hx.2).symm]
        simp
      rw [hsigcount, add_zero]
      have hmult := winf_eigenvalue_multiplicity M j
      have hconv : (Multiset.filter (fun a => g j = hA.eigenvalues a) Finset.univ.val).card
            = (Finset.univ.filter (fun i : Fin n => hA.eigenvalues i = g j)).card := by
        have hfe : (Finset.univ.filter (fun i : Fin n => g j = hA.eigenvalues i))
              = (Finset.univ.filter (fun i : Fin n => hA.eigenvalues i = g j)) := by
          apply Finset.filter_congr; intro x _; exact eq_comm
        rw [show (Multiset.filter (fun a => g j = hA.eigenvalues a) Finset.univ.val).card
              = (Finset.univ.filter (fun i : Fin n => g j = hA.eigenvalues i)).card from rfl, hfe]
      rw [hconv, hgdef]; exact hmult
    · push_neg at hcsig
      rw [if_neg (fun h => hcbulk h.symm), add_zero]
      have hsig0 : (Multiset.filter (fun a => c = g a) Finset.univ.val).card = 0 := by
        rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
        intro a _; exact fun h => hcsig a h
      rw [hsig0]
      -- Exhaustion: c is neither μ nor any g j, so c is not an eigenvalue of W∞.
      have hnot : ∀ i : Fin n, hA.eigenvalues i ≠ c :=
        winf_eigenvalue_not_c M c hcbulk hcsig
      have : (Multiset.filter (fun a => c = hA.eigenvalues a) Finset.univ.val) = 0 := by
        rw [Multiset.filter_eq_nil]
        intro a _ h; exact hnot a h.symm
      rw [this, Multiset.card_zero]

/-- For an antitone `σ : Fin n → ℝ`, the super-level set `{i | c < σ i}` is an
initial segment: `c < σ i` holds iff `(i : ℕ)` is below the cardinality of that set. -/
private lemma antitone_superlevel_initial {n : ℕ} (σ : Fin n → ℝ) (hσ : Antitone σ) (c : ℝ) :
    ∀ i : Fin n, (c < σ i) ↔
      (i : ℕ) < (Finset.univ.filter (fun i : Fin n => c < σ i)).card := by
  classical
  set A := Finset.univ.filter (fun i : Fin n => c < σ i) with hAdef
  -- A is a lower set: i ∈ A, i' ≤ i ⇒ i' ∈ A
  have hlower : ∀ {a b : Fin n}, a ∈ A → b ≤ a → b ∈ A := by
    intro a b ha hba
    rw [hAdef, Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ b, lt_of_lt_of_le ha.2 (hσ hba)⟩
  -- Characterize A = {i | (i:ℕ) < A.card}
  have hAeq : ∀ i : Fin n, i ∈ A ↔ (i : ℕ) < A.card := by
    intro i
    constructor
    · intro hi
      have hsub : Finset.Iic i ⊆ A := by
        intro b hb
        rw [Finset.mem_Iic] at hb
        exact hlower hi hb
      have hcard : (Finset.Iic i).card ≤ A.card := Finset.card_le_card hsub
      rw [Fin.card_Iic] at hcard
      omega
    · intro hi
      by_contra hnotmem
      have hsub : A ⊆ Finset.Iio i := by
        intro a ha
        rw [Finset.mem_Iio]
        by_contra hle
        push_neg at hle
        exact hnotmem (hlower ha hle)
      have hcard : A.card ≤ (Finset.Iio i).card := Finset.card_le_card hsub
      rw [Fin.card_Iio] at hcard
      omega
  intro i
  have hmemA : (c < σ i) ↔ i ∈ A := by rw [hAdef, Finset.mem_filter]; simp
  rw [hmemA]
  exact hAeq i

/-- **Simplicity of the `J`-th sorted eigenvalue of `W∞`.**  `W∞ = Φ̄∞ᵀΦ̄∞/n +
(δ²/n)I` is Hermitian; its sorted (antitone) eigenvalue list `σ` equals
`λ₁+δ²/n > ⋯ > λ_k+δ²/n > δ²/n = ⋯ = δ²/n`.  In particular, at the signal index
`J = castLE j` we have `σ J = λⱼ + δ²/n`, and this value occurs at exactly that one
index (`σ i ≠ σ J` for all `i ≠ J`).  Packaged with the Hermitian witness `hWinf`
and reindexing permutation `e'` so it plugs directly into `Fact2_Weyl`. -/
private lemma floor_Winf_simple {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (j : Fin k) :
    ∃ (hWinf : (Winf M).IsHermitian) (σ : Fin n → ℝ) (e' : Fin n ≃ Fin n),
      Antitone σ ∧
      (σ = fun i => hWinf.eigenvalues (e' i)) ∧
      σ (Fin.castLE (le_of_lt M.hkn) j) = M.lam j + δ2 / n ∧
      (∀ i : Fin n, i ≠ Fin.castLE (le_of_lt M.hkn) j →
        σ i ≠ M.lam j + δ2 / n) := by
  classical
  set hWinf := winf_hermitian M with hWinfdef
  set μ : ℝ := δ2 / n with hμdef
  -- The explicit sorted spectrum: signal values (λ i + δ²/n) at indices < k, bulk μ elsewhere.
  set σ : Fin n → ℝ := fun i => if h : (i : ℕ) < k then M.lam ⟨(i : ℕ), h⟩ + μ else μ
    with hσdef
  have hlampos : ∀ i, 0 < M.lam i := M.hlam_pos
  -- σ is antitone.
  have hσanti : Antitone σ := by
    intro a b hab
    have hab' : (a : ℕ) ≤ (b : ℕ) := hab
    simp only [hσdef]
    by_cases hb : (b : ℕ) < k
    · have ha : (a : ℕ) < k := lt_of_le_of_lt hab' hb
      rw [dif_pos ha, dif_pos hb]
      have hle : M.lam ⟨(b : ℕ), hb⟩ ≤ M.lam ⟨(a : ℕ), ha⟩ := by
        apply M.hlam_sorted.antitone
        exact hab'
      linarith
    · rw [dif_neg hb]
      by_cases ha : (a : ℕ) < k
      · rw [dif_pos ha]
        have := hlampos ⟨(a : ℕ), ha⟩
        linarith
      · rw [dif_neg ha]
  -- The value multiset of σ over all indices matches that of hWinf.eigenvalues.
  have hσmulti : Multiset.map σ Finset.univ.val
      = Multiset.map (fun i : Fin k => M.lam i + μ) Finset.univ.val
        + Multiset.replicate (n - k) μ := by
    apply Multiset.ext.mpr
    intro c
    rw [Multiset.count_map, Multiset.count_add, Multiset.count_map, Multiset.count_replicate]
    have key : (Multiset.filter (fun a => c = σ a) Finset.univ.val).card
        = (Multiset.filter (fun a : Fin k => c = M.lam a + μ) Finset.univ.val).card
          + (if c = μ then n - k else 0) := by
      rw [show (Multiset.filter (fun a => c = σ a) Finset.univ.val).card
            = (Finset.univ.filter (fun a : Fin n => c = σ a)).card from rfl]
      rw [show (Multiset.filter (fun a : Fin k => c = M.lam a + μ) Finset.univ.val).card
            = (Finset.univ.filter (fun a : Fin k => c = M.lam a + μ)).card from rfl]
      have hpart : (Finset.univ.filter (fun a : Fin n => c = σ a))
          = (Finset.univ.filter (fun a : Fin n => (a : ℕ) < k ∧ c = σ a))
            ∪ (Finset.univ.filter (fun a : Fin n => ¬ (a : ℕ) < k ∧ c = σ a)) := by
        ext a
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; by_cases hak : (a : ℕ) < k
          · exact Or.inl ⟨hak, h⟩
          · exact Or.inr ⟨hak, h⟩
        · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
      have hdisj : Disjoint (Finset.univ.filter (fun a : Fin n => (a : ℕ) < k ∧ c = σ a))
          (Finset.univ.filter (fun a : Fin n => ¬ (a : ℕ) < k ∧ c = σ a)) := by
        rw [Finset.disjoint_left]
        intro a ha ha'
        rw [Finset.mem_filter] at ha ha'
        exact ha'.2.1 ha.2.1
      rw [hpart, Finset.card_union_of_disjoint hdisj]
      congr 1
      · -- Count over i<k equals count over Fin k of c = lam a + μ.
        apply Finset.card_bij
          (fun (a : Fin n) (ha : a ∈ (Finset.univ.filter (fun a : Fin n => (a : ℕ) < k ∧ c = σ a))) =>
            (⟨(a : ℕ), (Finset.mem_filter.mp ha).2.1⟩ : Fin k))
        · intro a ha
          rw [Finset.mem_filter] at ha ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          have hval := ha.2.2
          simp only [hσdef, dif_pos ha.2.1] at hval
          exact hval
        · intro a ha a' ha' heq
          apply Fin.ext
          exact Fin.mk.inj heq
        · intro b hb
          rw [Finset.mem_filter] at hb
          refine ⟨⟨(b : ℕ), lt_of_lt_of_le b.2 (le_of_lt M.hkn)⟩, ?_, ?_⟩
          · rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, b.2, ?_⟩
            simp only [hσdef, dif_pos b.2]
            convert hb.2 using 3
          · apply Fin.ext; rfl
      · -- Count over i≥k of c=σ a = c=μ.
        by_cases hcμ : c = μ
        · rw [if_pos hcμ]
          rw [show (Finset.univ.filter (fun a : Fin n => ¬ (a : ℕ) < k ∧ c = σ a))
                = (Finset.univ.filter (fun a : Fin n => ¬ (a : ℕ) < k)) from by
            ext a
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
            intro hak
            simp only [hσdef, dif_neg hak]
            exact hcμ]
          have hkcard : (Finset.univ.filter (fun a : Fin n => (a : ℕ) < k)).card = k := by
            rw [show (Finset.univ.filter (fun a : Fin n => (a : ℕ) < k))
                  = Finset.map (Fin.castLEEmb (le_of_lt M.hkn)) Finset.univ from by
              ext a
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
                Fin.castLEEmb_apply]
              constructor
              · intro hak; exact ⟨⟨(a:ℕ), hak⟩, by apply Fin.ext; rfl⟩
              · rintro ⟨b, _, rfl⟩; exact b.2]
            rw [Finset.card_map]; simp
          have hcompl : (Finset.univ.filter (fun a : Fin n => ¬ (a : ℕ) < k)).card = n - k := by
            rw [Finset.filter_not, Finset.card_sdiff,
              Finset.card_univ, Fintype.card_fin]
            congr 1
            rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
            exact hkcard
          rw [hcompl]
        · rw [if_neg hcμ]
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro a _
          rintro ⟨hak, hca⟩
          simp only [hσdef, dif_neg hak] at hca
          exact hcμ hca
    rw [key]; congr 1; exact if_congr eq_comm rfl rfl
  -- Combine with winf_eigenvalues_multiset to equate the two value multisets.
  have hmulti : Multiset.map σ Finset.univ.val
      = Multiset.map hWinf.eigenvalues Finset.univ.val := by
    rw [hσmulti, hWinfdef, hμdef, winf_eigenvalues_multiset M]
  -- Build the reindexing permutation e' via fiber cardinalities.
  have H_fibers : ∀ y : ℝ,
      Fintype.card {i : Fin n // σ i = y}
        = Fintype.card {i : Fin n // hWinf.eigenvalues i = y} := by
    intro y
    have hcount : (Multiset.map σ Finset.univ.val).count y
        = (Multiset.map hWinf.eigenvalues Finset.univ.val).count y := by rw [hmulti]
    rw [Multiset.count_map, Multiset.count_map] at hcount
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rw [show (Finset.univ.filter (fun i : Fin n => σ i = y)).card
          = (Multiset.filter (fun a => σ a = y) Finset.univ.val).card from rfl]
    rw [show (Finset.univ.filter (fun i : Fin n => hWinf.eigenvalues i = y)).card
          = (Multiset.filter (fun a => hWinf.eigenvalues a = y) Finset.univ.val).card from rfl]
    simp only [eq_comm] at hcount ⊢
    exact hcount
  let sig_equiv : (f : Fin n → ℝ) → (Σ y : ℝ, {x : Fin n // f x = y}) ≃ Fin n :=
    fun f =>
    { toFun := fun s => s.2.val
      invFun := fun x => ⟨f x, ⟨x, rfl⟩⟩
      left_inv := by rintro ⟨y, ⟨x, hx⟩⟩; subst hx; rfl
      right_inv := fun x => rfl }
  let e_fiber : (y : ℝ) → {i : Fin n // σ i = y} ≃ {i : Fin n // hWinf.eigenvalues i = y} :=
    fun y => Fintype.equivOfCardEq (H_fibers y)
  let e' : Fin n ≃ Fin n :=
    (sig_equiv σ).symm.trans ((Equiv.sigmaCongrRight e_fiber).trans (sig_equiv hWinf.eigenvalues))
  have hσeig : σ = fun i => hWinf.eigenvalues (e' i) := by
    funext i
    show σ i = hWinf.eigenvalues (e' i)
    have hei : e' i = (e_fiber (σ i) ⟨i, rfl⟩).val := rfl
    rw [hei]
    exact ((e_fiber (σ i) ⟨i, rfl⟩).property).symm
  refine ⟨hWinf, σ, e', hσanti, hσeig, ?_, ?_⟩
  · -- σ (castLE j) = lam j + μ
    simp only [hσdef]
    have hcast : ((Fin.castLE (le_of_lt M.hkn) j : Fin n) : ℕ) = (j : ℕ) := rfl
    rw [dif_pos (by rw [hcast]; exact j.2)]
    congr 2
  · -- separation
    intro i hi
    simp only [hσdef]
    by_cases hik : (i : ℕ) < k
    · rw [dif_pos hik]
      intro hcontra
      have heq : M.lam ⟨(i : ℕ), hik⟩ = M.lam j := by
        have : M.lam ⟨(i : ℕ), hik⟩ + μ = M.lam j + μ := hcontra
        linarith
      have hij := M.hlam_sorted.injective heq
      apply hi
      apply Fin.ext
      rw [Fin.coe_castLE]
      exact congrArg Fin.val hij
    · rw [dif_neg hik]
      intro hcontra
      have := hlampos j
      have : M.lam j + μ = μ := hcontra.symm
      linarith

/-- **Simplicity of `θⱼ` in `W(p)` for large `p`.**  For all large `p`, `θⱼ^{(p,n)}`
is a simple eigenvalue of `W^{(p,n)} = YᵀY/(np)`: every unit vector `u` with
`W u = θⱼ u` equals `± wⱼ`. -/
private lemma floor_W_simple {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) (j : Fin k) :
    ∀ᶠ P : Adm k in atTop,
      ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
        Matrix.toEuclideanLin
            ((1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P))) u
          = M.θ P (Fin.castLE (le_of_lt M.hkn) j) • u →
        u = M.w P j ∨ u = -(M.w P j) := by
  classical
  set J : Fin n := Fin.castLE (le_of_lt M.hkn) j with hJdef
  -- Limit spectrum data for W∞.
  obtain ⟨hWinf, σ, e', hσanti, hσeq, hσJ, hσsep⟩ := floor_Winf_simple M j
  -- Minimal gap of σ away from σ J = lam j + δ²/n, over the finite set of i ≠ J.
  -- g > 0.
  set g : ℝ := Finset.inf' (Finset.univ.filter (fun i : Fin n => i ≠ J))
    (by
      refine Finset.filter_nonempty_iff.mpr ?_
      -- there is some i ≠ J since n ≥ 2 (k < n and 1 ≤ k ⇒ n ≥ 2)
      have hn2 : 2 ≤ n := by
        have := M.hk; have := M.hkn; omega
      -- pick i ≠ J : use that Fin n is not a subsingleton
      have : Nontrivial (Fin n) := by
        rw [Fin.nontrivial_iff_two_le]; exact hn2
      obtain ⟨i, hi⟩ := exists_ne J
      exact ⟨i, Finset.mem_univ i, hi⟩)
    (fun i => |σ i - (M.lam j + δ2 / n)|) with hgdef
  have hg_pos : 0 < g := by
    rw [hgdef]
    rw [Finset.lt_inf'_iff]
    intro i hi
    rw [Finset.mem_filter] at hi
    have := hσsep i hi.2
    have : σ i - (M.lam j + δ2 / n) ≠ 0 := sub_ne_zero.mpr this
    positivity
  -- Weyl inequality: |θ P i - σ i| ≤ opNorm (W(P) - W∞).
  -- eventually opNorm (W(P) - W∞) < g/2.
  have hop := floor_W_opconv M
  have hsmall : ∀ᶠ P : Adm k in atTop,
      opNorm ((1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P)) - Winf M) < g / 2 := by
    have hg2 : (0 : ℝ) < g / 2 := by positivity
    have := hop.eventually (eventually_lt_nhds hg2)
    -- opNorm ≥ 0, and → 0, so eventually < g/2
    filter_upwards [this] with P hP
    -- hP : opNorm ... ∈ Iio (g/2)?  Actually eventually_lt_nhds gives (fun x => x < g/2)∘id
    exact hP
  filter_upwards [hsmall] with P hPsmall
  intro u hu hue
  -- Establish separation of θ P J from θ P i for all i ≠ J, then apply
  -- hermitian_simple_eigvec_pm through hθ_spectrum.
  set θ := M.θ P with hθdef
  -- Weyl: obtain Hermitian witness hW and permutation e for W(P) from hθ_spectrum.
  obtain ⟨hW, e, hθeq⟩ := M.hθ_spectrum P
  -- Note: Ymat M P = (b P)*(Φ P) + Z P, so hW's matrix is exactly W(P).
  have hWymat : ((1 / ((n : ℝ) * P.1)) • (((M.b P) * (M.Φ P) + M.Z P)ᵀ *
      ((M.b P) * (M.Φ P) + M.Z P)))
      = (1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P)) := by
    simp [Ymat]
  -- Weyl inequality for each index i.
  have hweyl : ∀ i : Fin n,
      |θ i - σ i| ≤
        opNorm ((1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P)) - Winf M) := by
    intro i
    -- Apply Fact2_Weyl n to A = W∞, A' = W(P).
    have hA'herm : ((1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P))).IsHermitian := by
      rw [← hWymat]; exact hW
    have hσ'eq : θ = fun i => hA'herm.eigenvalues (e i) := by
      rw [hθdef, hθeq]
    exact hFact2n (Winf M) ((1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P)))
      hWinf hA'herm σ θ e' e hσanti (M.hθ_sorted P) hσeq hσ'eq i
  -- Now strict separation.
  have hsep : ∀ i : Fin n, i ≠ J → θ i ≠ θ J := by
    intro i hi
    -- |θ i - θ J| > 0
    have hbi := hweyl i
    have hbJ := hweyl J
    have hσi : |σ i - (M.lam j + δ2 / n)| ≥ g := by
      rw [hgdef]
      exact Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    -- hbJ : |θ J - σ J| ≤ ...; rewrite σ J = lam j + δ2/n
    have hσJ' : σ J = M.lam j + δ2 / n := hσJ
    rw [hσJ'] at hbJ
    -- |θ i - θ J| ≥ |σ i - σ J| - |θ i - σ i| - |θ J - σ J| > g - g/2 - g/2 = 0
    have key : |θ i - θ J| > 0 := by
      have e1 : |σ i - (M.lam j + δ2 / n)| ≤ |θ i - σ i| + |θ i - θ J|
          + |θ J - (M.lam j + δ2 / n)| := by
        calc |σ i - (M.lam j + δ2 / n)|
            = |(-(θ i - σ i)) + (θ i - θ J) + (θ J - (M.lam j + δ2 / n))| := by
              congr 1; ring
          _ ≤ |(-(θ i - σ i)) + (θ i - θ J)| + |θ J - (M.lam j + δ2 / n)| :=
              abs_add_le _ _
          _ ≤ (|(-(θ i - σ i))| + |θ i - θ J|) + |θ J - (M.lam j + δ2 / n)| := by
              gcongr
              exact abs_add_le _ _
          _ = |θ i - σ i| + |θ i - θ J| + |θ J - (M.lam j + δ2 / n)| := by
              rw [abs_neg]
      have hb1 : |θ i - σ i| < g / 2 := lt_of_le_of_lt hbi hPsmall
      have hb2 : |θ J - (M.lam j + δ2 / n)| < g / 2 := lt_of_le_of_lt hbJ hPsmall
      have hgeq : |σ i - (M.lam j + δ2 / n)| ≥ g := hσi
      linarith [hgeq, e1, hb1, hb2]
    intro h
    rw [h] at key
    simp at key
  -- Translate to hW eigenvalues at i₀ = e J and apply the spectral simplicity lemma.
  set μ : ℝ := θ J with hμdef
  set i₀ : Fin n := e J with hi0def
  have hμeq : hW.eigenvalues i₀ = μ := by
    rw [hμdef, hθdef, hθeq]
  have hsepμ : ∀ m : Fin n, m ≠ i₀ → hW.eigenvalues m ≠ μ := by
    intro m hm
    -- m = e i for i = e.symm m, i ≠ J
    have hmi : m = e (e.symm m) := (e.apply_symm_apply m).symm
    have hine : e.symm m ≠ J := by
      intro h
      apply hm
      rw [hi0def, ← h, e.apply_symm_apply]
    have : θ (e.symm m) ≠ θ J := hsep (e.symm m) hine
    intro hcontra
    apply this
    -- θ (e.symm m) = hW.eigenvalues (e (e.symm m)) = hW.eigenvalues m = μ = θ J
    have : θ (e.symm m) = hW.eigenvalues m := by
      rw [hθdef, hθeq]; simp
    rw [this, hcontra, hμdef]
  -- w P j is unit eigenvector of W(P) at μ = θ J.
  have hwe : Matrix.toEuclideanLin ((1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P)))
      (M.w P j) = μ • (M.w P j) := by
    have := M.hw_eig P j
    rw [hWymat] at this
    rw [hμdef, hθdef, hJdef]
    exact this
  -- u is unit eigenvector at μ.
  have hueμ : Matrix.toEuclideanLin ((1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P)))
      u = μ • u := by
    rw [hμdef, hθdef, hJdef]; exact hue
  -- Apply the spectral simplicity lemma with A = W(P) matrix, hW witness.
  have hAeq : ((1 / ((n : ℝ) * P.1)) • ((Ymat M P)ᵀ * (Ymat M P)))
      = ((1 / ((n : ℝ) * P.1)) • (((M.b P) * (M.Φ P) + M.Z P)ᵀ *
        ((M.b P) * (M.Φ P) + M.Z P))) := hWymat.symm
  -- rewrite eigen-equations to the hW matrix form
  rw [hAeq] at hwe hueμ
  exact hermitian_simple_eigvec_pm _ hW i₀ μ hμeq hsepμ (M.w P j) (M.hw_unit P j)
    hwe u hu hueμ

private lemma floor_parallel {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) (j : Fin k) :
    ∀ᶠ P : Adm k in atTop,
      ∃ c : ℝ, M.h P j
        = c • Matrix.toEuclideanLin (Ymat M P) (M.w P j) := by
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  have hsimple := floor_W_simple M hFact1 hFact2n hFact3n hFact2k hFact3k j
  have hθpos : ∀ᶠ P : Adm k in atTop,
      0 < M.θ P (Fin.castLE (le_of_lt M.hkn) j) := by
    have hlim := M.field4_dualSpectrum j
    have hpos : (0 : ℝ) < M.lam j + δ2 / n := by
      have := M.hlam_pos j; have := M.hδ2; positivity
    exact hlim.eventually (eventually_gt_nhds hpos)
  filter_upwards [hsimple, hθpos] with P hsimple hθpos
  set θ : ℝ := M.θ P (Fin.castLE (le_of_lt M.hkn) j) with hθdef
  set p : ℝ := (P.1 : ℝ) with hpdef
  have hp : (0 : ℝ) < p := by
    have : (0 : ℕ) < P.1 := lt_of_lt_of_le M.hk P.2
    rw [hpdef]; exact_mod_cast this
  set Y := Ymat M P with hYdef
  set w := M.w P j with hwdef
  set h := M.h P j with hhdef
  have hnp : ((n : ℝ) * p) ≠ 0 := by positivity
  have hθne : θ ≠ 0 := ne_of_gt hθpos
  -- S h = θ h : from hh_eig
  have hSh : Matrix.toEuclideanLin ((1 / ((n : ℝ) * P.1)) • (Y * Yᵀ)) h = θ • h := by
    have := M.hh_eig P j
    simpa [Ymat, hYdef, hhdef, hθdef] using this
  -- W (Yᵀ h) = θ (Yᵀ h)
  have hWv : Matrix.toEuclideanLin ((1 / ((n : ℝ) * P.1)) • (Yᵀ * Y))
      (Matrix.toEuclideanLin Yᵀ h) = θ • Matrix.toEuclideanLin Yᵀ h := by
    have hmat : ((1 / ((n : ℝ) * P.1)) • (Yᵀ * Y)) * Yᵀ
        = Yᵀ * ((1 / ((n : ℝ) * P.1)) • (Y * Yᵀ)) := by
      rw [Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      rw [Matrix.mul_assoc]
    calc Matrix.toEuclideanLin ((1 / ((n : ℝ) * P.1)) • (Yᵀ * Y))
            (Matrix.toEuclideanLin Yᵀ h)
        = Matrix.toEuclideanLin (((1 / ((n : ℝ) * P.1)) • (Yᵀ * Y)) * Yᵀ) h :=
          toEuclideanLin_comp _ _ _
      _ = Matrix.toEuclideanLin (Yᵀ * ((1 / ((n : ℝ) * P.1)) • (Y * Yᵀ))) h := by
          rw [hmat]
      _ = Matrix.toEuclideanLin Yᵀ
            (Matrix.toEuclideanLin ((1 / ((n : ℝ) * P.1)) • (Y * Yᵀ)) h) :=
          (toEuclideanLin_comp _ _ _).symm
      _ = Matrix.toEuclideanLin Yᵀ (θ • h) := by rw [hSh]
      _ = θ • Matrix.toEuclideanLin Yᵀ h := by rw [map_smul]
  -- Yᵀ h parallel to w
  obtain ⟨d, hd⟩ := eigenvector_parallel_of_simple
    ((1 / ((n : ℝ) * P.1)) • (Yᵀ * Y)) θ w (Matrix.toEuclideanLin Yᵀ h)
    (M.hw_unit P j) hsimple hWv
  -- h = (d/(np θ)) • Y w
  refine ⟨d / ((n : ℝ) * p * θ), ?_⟩
  -- toEuclideanLin ((1/np)•(Y*Yᵀ)) h = (1/np) • toEuclideanLin (Y*Yᵀ) h
  have hSh' : (1 / ((n : ℝ) * P.1)) •
      Matrix.toEuclideanLin (Y * Yᵀ) h = θ • h := by
    have hmap : Matrix.toEuclideanLin ((1 / ((n : ℝ) * P.1)) • (Y * Yᵀ)) h
        = (1 / ((n : ℝ) * P.1)) • Matrix.toEuclideanLin (Y * Yᵀ) h := by
      rw [map_smul]
      rfl
    rw [← hmap]; exact hSh
  -- toEuclideanLin (Y*Yᵀ) h = toEuclideanLin Y (toEuclideanLin Yᵀ h) = d • toEuclideanLin Y w
  have hYYh : Matrix.toEuclideanLin (Y * Yᵀ) h
      = d • Matrix.toEuclideanLin Y w := by
    rw [← toEuclideanLin_comp, hd, map_smul]
  rw [hYYh, smul_smul] at hSh'
  -- hSh' : ((1/np) * d) • toEuclideanLin Y w = θ • h
  have hkey : h = θ⁻¹ • (((1 / ((n : ℝ) * P.1)) * d) • Matrix.toEuclideanLin Y w) := by
    rw [hSh', smul_smul, inv_mul_cancel₀ hθne, one_smul]
  rw [hkey, smul_smul]
  congr 1
  rw [hpdef]
  field_simp

/-- **Floor sub-lemma A (primal/dual bridge, squared-norm form).**  For all large
`p`, `‖Π⊥ hⱼ‖² = ‖Π⊥ (Z wⱼ)‖² / (n p θⱼ)`, where `Π⊥ = I − b bᵀ`.  Derived from
`floor_parallel` (parallelism `hⱼ ∥ Y wⱼ`) plus the norm computation
`‖Y wⱼ‖² = n p θⱼ` and the projector identity `Π⊥ Y = Π⊥ Z`. -/
private lemma floor_bridge {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) (j : Fin k) :
    ∀ᶠ P : Adm k in atTop,
      ‖Matrix.toEuclideanLin (1 - (M.b P) * (M.b P)ᵀ) (M.h P j)‖ ^ 2
        = ‖Matrix.toEuclideanLin (1 - (M.b P) * (M.b P)ᵀ)
              (Matrix.toEuclideanLin (M.Z P) (M.w P j))‖ ^ 2
          / (((n : ℝ) * P.1) * M.θ P (Fin.castLE (le_of_lt M.hkn) j)) := by
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  have hpar := floor_parallel M hFact1 hFact2n hFact3n hFact2k hFact3k j
  -- θⱼ > 0 eventually (θⱼ → λⱼ + δ²/n > 0)
  have hθpos : ∀ᶠ P : Adm k in atTop,
      0 < M.θ P (Fin.castLE (le_of_lt M.hkn) j) := by
    have hlim := M.field4_dualSpectrum j
    have hpos : (0 : ℝ) < M.lam j + δ2 / n := by
      have := M.hlam_pos j; have := M.hδ2; positivity
    exact hlim.eventually (eventually_gt_nhds hpos)
  filter_upwards [hpar, hθpos] with P hpar hθpos
  obtain ⟨c, hc⟩ := hpar
  set p : ℝ := (P.1 : ℝ) with hpdef
  set θ : ℝ := M.θ P (Fin.castLE (le_of_lt M.hkn) j) with hθdef
  set Pp : Matrix (Fin P.1) (Fin P.1) ℝ := 1 - (M.b P) * (M.b P)ᵀ with hPpdef
  have hp : (0 : ℝ) < p := by
    have : (0 : ℕ) < P.1 := lt_of_lt_of_le M.hk P.2
    rw [hpdef]; exact_mod_cast this
  have hbo : (M.b P)ᵀ * (M.b P) = 1 := M.hb_ortho P
  -- (n2) matrix identity: Pp * (Ymat) = Pp * Z
  have hmatid : Pp * (Ymat M P) = Pp * (M.Z P) := by
    rw [hPpdef, Ymat, Matrix.mul_add]
    have hbz : ((1 : Matrix (Fin P.1) (Fin P.1) ℝ) - (M.b P) * (M.b P)ᵀ) * (M.b P * M.Φ P) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      rw [← Matrix.mul_assoc ((M.b P) * (M.b P)ᵀ) (M.b P) (M.Φ P)]
      rw [Matrix.mul_assoc (M.b P) (M.b P)ᵀ (M.b P), hbo, Matrix.mul_one, sub_self]
    rw [hbz, zero_add]
  -- (n2') the linear map version
  have hn2 : Matrix.toEuclideanLin Pp (Matrix.toEuclideanLin (Ymat M P) (M.w P j))
      = Matrix.toEuclideanLin Pp (Matrix.toEuclideanLin (M.Z P) (M.w P j)) := by
    rw [toEuclideanLin_comp, toEuclideanLin_comp, hmatid]
  -- (n1) ‖Ymat w‖² = np θ
  have hn1 : ‖Matrix.toEuclideanLin (Ymat M P) (M.w P j)‖ ^ 2 = (n : ℝ) * p * θ := by
    rw [normSq_toEuclideanLin]
    -- toEuclideanLin (Yᵀ*Y) w = (np θ) • w
    have heig := M.hw_eig P j
    -- heig : toEuclideanLin ((1/(np))•(YᵀY)) w = θ • w
    have hscale : Matrix.toEuclideanLin ((Ymat M P)ᵀ * (Ymat M P)) (M.w P j)
        = ((n : ℝ) * p * θ) • (M.w P j) := by
      have hnp : ((n : ℝ) * P.1) ≠ 0 := by
        have : (0 : ℝ) < (n : ℝ) * p := by positivity
        rw [hpdef] at this; exact ne_of_gt this
      have := heig
      simp only [Ymat] at this ⊢
      rw [map_smul, LinearMap.smul_apply] at this
      -- this : (1/(np)) • toEuclideanLin (YᵀY) w = θ • w
      have hlin : Matrix.toEuclideanLin (((M.b P) * (M.Φ P) + M.Z P)ᵀ * ((M.b P) * (M.Φ P) + M.Z P)) (M.w P j)
          = ((n : ℝ) * P.1) • (θ • M.w P j) := by
        have := congrArg (fun x => ((n : ℝ) * P.1) • x) this
        simp only at this
        rw [smul_smul] at this
        rw [one_div, mul_inv_cancel₀ hnp, one_smul] at this
        exact this
      rw [hlin, smul_smul]
    rw [hscale, inner_smul_right]
    have hwu : ‖M.w P j‖ = 1 := M.hw_unit P j
    rw [real_inner_self_eq_norm_sq, hwu]
    ring
  -- (n3) ‖h‖ = 1, and relation to c²
  have hhu : ‖M.h P j‖ = 1 := M.hh_unit P j
  have hnpθpos : (0 : ℝ) < (n : ℝ) * p * θ := by positivity
  -- from hc: ‖h‖² = c² * ‖Y w‖² = c² * (npθ)
  have hcsq : c ^ 2 * ((n : ℝ) * p * θ) = 1 := by
    have : ‖M.h P j‖ ^ 2 = c ^ 2 * ‖Matrix.toEuclideanLin (Ymat M P) (M.w P j)‖ ^ 2 := by
      rw [hc, norm_smul, mul_pow]
      congr 1
      rw [Real.norm_eq_abs, sq_abs]
    rw [hhu, hn1] at this
    linarith [this]
  -- now assemble
  rw [hc, map_smul, norm_smul, mul_pow, hn2]
  rw [Real.norm_eq_abs, sq_abs]
  -- goal: c^2 * ‖Pp (Z w)‖^2 = ‖Pp (Z w)‖^2 / (np θ)
  rw [eq_div_iff (ne_of_gt hnpθpos)]
  -- c^2 * X * (npθ) = X  where c^2*(npθ)=1
  have : c ^ 2 * ‖Matrix.toEuclideanLin Pp (Matrix.toEuclideanLin (M.Z P) (M.w P j))‖ ^ 2
      * ((n : ℝ) * p * θ)
      = (c ^ 2 * ((n : ℝ) * p * θ)) * ‖Matrix.toEuclideanLin Pp (Matrix.toEuclideanLin (M.Z P) (M.w P j))‖ ^ 2 := by
    ring
  rw [this, hcsq, one_mul]

/-- **Floor sub-lemma B (numerator limit).**  `‖Π⊥ (Z wⱼ)‖² / (n p) → δ²/n`.

`‖Π⊥ Z wⱼ‖² = wⱼᵀ (Zᵀ Π⊥ Z) wⱼ`, and `Zᵀ Π⊥ Z /(np) = ZᵀZ/(np) − (bᵀZ)ᵀ(bᵀZ)/(np)`.
`ZᵀZ/(np) → (δ²/n)Iₙ` (`field1_noiseGram`); `(bᵀZ)/√p → 0` (`field2_decoherence`)
kills the second term; `wⱼ → wⱼ^{(n)}` (`field5_dualEigvec`) is unit, so the
quadratic form tends to `(δ²/n)‖wⱼ^{(n)}‖² = δ²/n`. -/
private lemma floor_numer {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) (j : Fin k) :
    Tendsto
      (fun P : Adm k =>
        ‖Matrix.toEuclideanLin (1 - (M.b P) * (M.b P)ᵀ)
              (Matrix.toEuclideanLin (M.Z P) (M.w P j))‖ ^ 2
          / ((n : ℝ) * P.1))
      atTop (𝓝 (δ2 / n)) := by
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn
  -- The value function expressed as a quadratic form `X ⬝ᵥ (G P *ᵥ X)`, with
  -- `X = ofLp (w P j)` and `G P = (1/np)•ZᵀZ - (1/np)•(bᵀZ)ᵀ(bᵀZ)`.
  set G : Adm k → Matrix (Fin n) (Fin n) ℝ := fun P =>
    (1 / ((n : ℝ) * P.1)) • ((M.Z P)ᵀ * (M.Z P))
      - (1 / ((n : ℝ) * P.1)) • (((M.b P)ᵀ * (M.Z P))ᵀ * ((M.b P)ᵀ * (M.Z P)))
    with hGdef
  -- Pointwise identity.
  have hpoint : ∀ P : Adm k,
      ‖Matrix.toEuclideanLin (1 - (M.b P) * (M.b P)ᵀ)
              (Matrix.toEuclideanLin (M.Z P) (M.w P j))‖ ^ 2
          / ((n : ℝ) * P.1)
        = (WithLp.ofLp (M.w P j)) ⬝ᵥ (G P *ᵥ WithLp.ofLp (M.w P j)) := by
    intro P
    set Z := M.Z P
    set b := M.b P
    set w := M.w P j
    set X : Fin n → ℝ := WithLp.ofLp w with hXdef
    set M0 : Matrix (Fin P.1) (Fin P.1) ℝ := 1 - b * bᵀ with hM0def
    have hbo : bᵀ * b = 1 := M.hb_ortho P
    -- symmetry and idempotence of M0
    have hM0symm : M0ᵀ = M0 := by
      rw [hM0def, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.transpose_transpose]
    have hM0idem : M0ᵀ * M0 = M0 := by
      rw [hM0symm, hM0def, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
        Matrix.mul_one]
      have : (b * bᵀ) * (b * bᵀ) = b * bᵀ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc bᵀ b bᵀ, hbo, Matrix.one_mul]
      rw [this]; abel
    -- ‖y‖² as dotProduct
    have hnorm : ‖Matrix.toEuclideanLin M0 (Matrix.toEuclideanLin Z w)‖ ^ 2
        = (M0 *ᵥ (Z *ᵥ X)) ⬝ᵥ (M0 *ᵥ (Z *ᵥ X)) := by
      rw [← real_inner_self_eq_norm_sq]
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      rw [Matrix.piLp_ofLp_toEuclideanLin]
      simp only [Matrix.toLin'_apply, star_trivial]
      rw [Matrix.piLp_ofLp_toEuclideanLin]
      simp only [Matrix.toLin'_apply]
      rw [dotProduct_comm]
    rw [hnorm]
    -- fold to u ⬝ᵥ (M0 *ᵥ u)
    set u : Fin P.1 → ℝ := Z *ᵥ X with hudef
    have hfold : (M0 *ᵥ u) ⬝ᵥ (M0 *ᵥ u) = u ⬝ᵥ (M0 *ᵥ u) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
        Matrix.mulVec_mulVec, hM0idem]
    rw [hfold]
    -- expand M0 *ᵥ u = u - b *ᵥ (bᵀ *ᵥ u)
    have hexp : M0 *ᵥ u = u - b *ᵥ (bᵀ *ᵥ u) := by
      rw [hM0def, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    rw [hexp, dotProduct_sub]
    -- u ⬝ᵥ (b *ᵥ (bᵀ *ᵥ u)) = (bᵀ *ᵥ u) ⬝ᵥ (bᵀ *ᵥ u)
    have hproj : u ⬝ᵥ (b *ᵥ (bᵀ *ᵥ u)) = (bᵀ *ᵥ u) ⬝ᵥ (bᵀ *ᵥ u) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [hproj]
    -- now express both terms as X ⬝ᵥ (matrix *ᵥ X)
    have hu2 : u ⬝ᵥ u = X ⬝ᵥ ((Zᵀ * Z) *ᵥ X) := by
      rw [hudef, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        dotProduct_comm, Matrix.mulVec_mulVec]
    have hbu : bᵀ *ᵥ u = (bᵀ * Z) *ᵥ X := by
      rw [hudef, Matrix.mulVec_mulVec]
    have hbu2 : (bᵀ *ᵥ u) ⬝ᵥ (bᵀ *ᵥ u)
        = X ⬝ᵥ (((bᵀ * Z)ᵀ * (bᵀ * Z)) *ᵥ X) := by
      rw [hbu, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        dotProduct_comm, Matrix.mulVec_mulVec]
    rw [hu2, hbu2]
    -- combine with the scalar 1/(np) into G
    rw [hGdef]
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      smul_eq_mul]
    ring
  -- Now the limit of the quadratic form.
  -- G P → (δ²/n) • 1.
  have hZZ : Tendsto (fun P : Adm k => (1 / ((n : ℝ) * P.1)) • ((M.Z P)ᵀ * (M.Z P)))
      atTop (𝓝 ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ))) := M.field1_noiseGram
  -- second term → 0
  have hbZ : Tendsto (fun P : Adm k => (1 / Real.sqrt P.1) • ((M.b P)ᵀ * (M.Z P)))
      atTop (𝓝 (0 : Matrix (Fin k) (Fin n) ℝ)) := M.field2_decoherence
  have hbZ2 : Tendsto
      (fun P : Adm k => (1 / ((n : ℝ) * P.1)) •
        (((M.b P)ᵀ * (M.Z P))ᵀ * ((M.b P)ᵀ * (M.Z P))))
      atTop (𝓝 (0 : Matrix (Fin n) (Fin n) ℝ)) := by
    -- rewrite as (1/n) • (Q P)ᵀ * (Q P) with Q P = (1/√p) • bᵀZ
    have heq : ∀ P : Adm k, (1 / ((n : ℝ) * P.1)) •
        (((M.b P)ᵀ * (M.Z P))ᵀ * ((M.b P)ᵀ * (M.Z P)))
        = (1 / (n : ℝ)) • (((1 / Real.sqrt P.1) • ((M.b P)ᵀ * (M.Z P)))ᵀ
            * ((1 / Real.sqrt P.1) • ((M.b P)ᵀ * (M.Z P)))) := by
      intro P
      have hp : (0 : ℝ) < P.1 := by
        have : (0 : ℕ) < P.1 := lt_of_lt_of_le M.hk P.2
        exact_mod_cast this
      have hsq : Real.sqrt P.1 * Real.sqrt P.1 = (P.1 : ℝ) :=
        Real.mul_self_sqrt (le_of_lt hp)
      rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul]
      congr 1
      symm
      rw [mul_assoc, div_mul_div_comm, one_mul, hsq, div_mul_div_comm, one_mul]
    rw [tendsto_congr heq]
    have hcont : Continuous fun A : Matrix (Fin k) (Fin n) ℝ => Aᵀ * A :=
      (continuous_id.matrix_transpose).matrix_mul continuous_id
    have hmul : Tendsto
        (fun P : Adm k => ((1 / Real.sqrt P.1) • ((M.b P)ᵀ * (M.Z P)))ᵀ
            * ((1 / Real.sqrt P.1) • ((M.b P)ᵀ * (M.Z P))))
        atTop (𝓝 ((0 : Matrix (Fin k) (Fin n) ℝ)ᵀ * (0 : Matrix (Fin k) (Fin n) ℝ))) :=
      (hcont.tendsto _).comp hbZ
    simp only [Matrix.transpose_zero, Matrix.zero_mul] at hmul
    have := hmul.const_smul (1 / (n : ℝ))
    simpa using this
  have hG : Tendsto G atTop (𝓝 ((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
    rw [hGdef]
    have := hZZ.sub hbZ2
    simpa using this
  -- w P j → wn j, hence ofLp (w P j) → ofLp (wn j)
  have hw : Tendsto (fun P : Adm k => M.w P j) atTop (𝓝 (M.wn j)) :=
    M.field5_dualEigvec j
  have hwof : Tendsto (fun P : Adm k => WithLp.ofLp (M.w P j)) atTop
      (𝓝 (WithLp.ofLp (M.wn j))) :=
    ((PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).tendsto _).comp hw
  -- continuity of the quadratic form (A, v) ↦ v ⬝ᵥ (A *ᵥ v)
  have hquad : Tendsto (fun P : Adm k =>
      (WithLp.ofLp (M.w P j)) ⬝ᵥ (G P *ᵥ WithLp.ofLp (M.w P j)))
      atTop (𝓝 ((WithLp.ofLp (M.wn j)) ⬝ᵥ
        (((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ WithLp.ofLp (M.wn j)))) := by
    have hcont : Continuous fun q : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) =>
        q.2 ⬝ᵥ (q.1 *ᵥ q.2) :=
      (continuous_snd).dotProduct ((continuous_fst).matrix_mulVec continuous_snd)
    have hpair : Tendsto (fun P : Adm k => (G P, WithLp.ofLp (M.w P j))) atTop
        (𝓝 (((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ)), WithLp.ofLp (M.wn j))) :=
      hG.prodMk_nhds hwof
    exact (hcont.tendsto _).comp hpair
  -- compute the limit value = δ²/n
  have hval : (WithLp.ofLp (M.wn j)) ⬝ᵥ
      (((δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ WithLp.ofLp (M.wn j))
      = δ2 / n := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      smul_eq_mul]
    have hwn : ‖M.wn j‖ = 1 := M.hwn_unit j
    have : (WithLp.ofLp (M.wn j)) ⬝ᵥ (WithLp.ofLp (M.wn j)) = ‖M.wn j‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
      simp [star_trivial]
    rw [this, hwn]; ring
  rw [hval] at hquad
  exact hquad.congr (fun P => (hpoint P).symm)

private lemma floor_limit {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) (j : Fin k) :
    Tendsto
      (fun P : Adm k =>
        ‖Matrix.toEuclideanLin (1 - (M.b P) * (M.b P)ᵀ) (M.h P j)‖ ^ 2)
      atTop (𝓝 (δ2 / ((n : ℝ) * M.lam j + δ2))) := by
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  have hlam := M.hlam_pos j
  have hδ := M.hδ2
  have hbridge := floor_bridge M hFact1 hFact2n hFact3n hFact2k hFact3k j
  have hnumer := floor_numer M hFact1 hFact2n hFact3n hFact2k hFact3k j
  have hθ := M.field4_dualSpectrum j
  have hθne : M.lam j + δ2 / n ≠ 0 := by positivity
  -- N P / θ P → (δ²/n)/(λⱼ+δ²/n)
  have hdiv := hnumer.div hθ hθne
  -- normalize the limit value
  have hval : (δ2 / n) / (M.lam j + δ2 / n) = δ2 / ((n : ℝ) * M.lam j + δ2) := by
    rw [eq_div_iff (by positivity)]
    field_simp
  rw [hval] at hdiv
  -- rewrite the goal function to N/θ eventually, then apply hdiv
  refine hdiv.congr' ?_
  filter_upwards [hbridge] with P hP
  simp only [Pi.div_apply]
  rw [hP]
  ring

/-- **Pointwise projection-norm identity.**  With `cⱼ := bᵀ hⱼ` and
`Π⊥ = I − b bᵀ`, `‖cⱼ‖² = 1 − ‖Π⊥ hⱼ‖²` (Pythagoras + `b` isometry). -/
private lemma cvec_normSq_eq {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2) (j : Fin k)
    (P : Adm k) :
    ‖Matrix.toEuclideanLin (M.b P)ᵀ (M.h P j)‖ ^ 2
      = 1 - ‖Matrix.toEuclideanLin (1 - M.b P * (M.b P)ᵀ) (M.h P j)‖ ^ 2 := by
  set b := M.b P with hb_def
  set hj := M.h P j with hj_def
  set cvec := Matrix.toEuclideanLin bᵀ hj with hcvec
  have hbortho : bᵀ * b = 1 := M.hb_ortho P
  have hhunit : ‖hj‖ = 1 := M.hh_unit P j
  -- adjoint identity: ⟨hj, toEuclideanLin b y⟩ = ⟨toEuclideanLin bᵀ hj, y⟩
  have hadj : ∀ y : EuclideanSpace ℝ (Fin k),
      (inner ℝ hj (Matrix.toEuclideanLin b y) : ℝ)
        = inner ℝ (Matrix.toEuclideanLin bᵀ hj) y := by
    intro y
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    rw [Matrix.piLp_ofLp_toEuclideanLin, Matrix.piLp_ofLp_toEuclideanLin]
    simp only [Matrix.toLin'_apply, star_trivial]
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  -- Π hj = toEuclideanLin (b*bᵀ) hj = toEuclideanLin b (cvec)
  have hProj : Matrix.toEuclideanLin (b * bᵀ) hj = Matrix.toEuclideanLin b cvec := by
    rw [hcvec, toEuclideanLin_comp]
  have hPnorm : ‖Matrix.toEuclideanLin (b * bᵀ) hj‖ = ‖cvec‖ := by
    rw [hProj, norm_toEuclideanLin_ortho b hbortho]
  have hsplit : Matrix.toEuclideanLin (1 - b * bᵀ) hj
      = hj - Matrix.toEuclideanLin (b * bᵀ) hj := by
    ext i
    simp only [Matrix.toEuclideanLin_apply, PiLp.sub_apply, Matrix.sub_mulVec,
      Matrix.one_mulVec, Pi.sub_apply]
  have hinner_proj : (inner ℝ hj (Matrix.toEuclideanLin (b * bᵀ) hj) : ℝ)
      = ‖cvec‖ ^ 2 := by
    rw [hProj, hadj cvec, hcvec, real_inner_self_eq_norm_sq]
  have hPerp : ‖Matrix.toEuclideanLin (1 - b * bᵀ) hj‖ ^ 2 = 1 - ‖cvec‖ ^ 2 := by
    rw [hsplit, ← real_inner_self_eq_norm_sq]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    rw [real_inner_self_eq_norm_sq, hhunit]
    rw [real_inner_self_eq_norm_sq, hPnorm]
    have hcross : (inner ℝ (Matrix.toEuclideanLin (b * bᵀ) hj) hj : ℝ) = ‖cvec‖ ^ 2 := by
      rw [real_inner_comm, hinner_proj]
    rw [hcross, hinner_proj]
    ring
  rw [hPerp]; ring

/-- **`‖cⱼ‖²` limit.**  `‖cⱼ‖² = ‖bᵀ hⱼ‖² → n λⱼ/(n λⱼ + δ²)`. -/
private lemma cvec_normSq_limit {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) (j : Fin k) :
    Tendsto (fun P : Adm k => ‖Matrix.toEuclideanLin (M.b P)ᵀ (M.h P j)‖ ^ 2)
      atTop (𝓝 ((n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2))) := by
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  have hlam := M.hlam_pos j
  have hδ := M.hδ2
  have hfloor := floor_limit M hFact1 hFact2n hFact3n hFact2k hFact3k j
  -- 1 - floor → 1 - δ²/(nλⱼ+δ²) = nλⱼ/(nλⱼ+δ²)
  have hcs : Tendsto
      (fun P : Adm k =>
        1 - ‖Matrix.toEuclideanLin (1 - M.b P * (M.b P)ᵀ) (M.h P j)‖ ^ 2)
      atTop (𝓝 (1 - δ2 / ((n : ℝ) * M.lam j + δ2))) := hfloor.const_sub 1
  have hval : (1 : ℝ) - δ2 / ((n : ℝ) * M.lam j + δ2)
      = (n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2) := by
    have hpos : (0 : ℝ) < (n : ℝ) * M.lam j + δ2 := by positivity
    field_simp
    ring
  rw [hval] at hcs
  refine hcs.congr' ?_
  filter_upwards with P
  exact (cvec_normSq_eq M j P).symm

/-- **`sinSq (cⱼ, eⱼ)` limit.**  The (sign-free) angle of `cⱼ = bᵀ hⱼ` to `eⱼ`
converges to that of `νⱼ^{(n)}`:  `sin²∠(cⱼ, eⱼ) → sin²∠(νⱼ^{(n)}, eⱼ)`. -/
private lemma cvec_sinSq_limit {k n : ℕ} {δ2 : ℝ} (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) (j : Fin k) :
    Tendsto (fun P : Adm k =>
        sinSq (Matrix.toEuclideanLin (M.b P)ᵀ (M.h P j))
          (EuclideanSpace.single j (1 : ℝ)))
      atTop (𝓝 (sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ)))) := by
  -- Notation.
  have hn : (0 : ℝ) < n := by
    have : (0 : ℕ) < n :=
      lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
    exact_mod_cast this
  set ej : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single j (1 : ℝ) with hej
  set L : ℝ := Real.sqrt ((n : ℝ) * M.lam j) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; apply Real.sqrt_pos.mpr; have := M.hlam_pos j; positivity
  have hLne : L ≠ 0 := ne_of_gt hLpos
  -- `ej ≠ 0` and `νn j ≠ 0`.
  have hej_norm : ‖ej‖ = 1 := by rw [hej, EuclideanSpace.norm_single]; norm_num
  have hej_ne : ej ≠ 0 := by
    intro h; rw [h, norm_zero] at hej_norm; norm_num at hej_norm
  have hνn_ne : M.νn j ≠ 0 := by
    rw [← norm_ne_zero_iff, M.hνn_unit j]; norm_num
  have hLνn_ne : L • M.νn j ≠ 0 := smul_ne_zero hLne hνn_ne
  -- Step 1: reduce the target limit value.
  have hval : sinSq (M.νn j) ej = sinSq (L • M.νn j) ej :=
    (sinSq_smul_left L hLne _ _).symm
  rw [hval]
  -- Step 2: define the approximating vector `uP`.
  set uP : Adm k → EuclideanSpace ℝ (Fin k) := fun P =>
    Matrix.toEuclideanLin
      (((1 / Real.sqrt P.1) • M.Φ P) + ((1 / Real.sqrt P.1) • ((M.b P)ᵀ * M.Z P)))
      (M.w P j) with huP
  -- θⱼ > 0 eventually.
  have hθpos : ∀ᶠ P : Adm k in atTop,
      0 < M.θ P (Fin.castLE (le_of_lt M.hkn) j) := by
    have hlim := M.field4_dualSpectrum j
    have hpos : (0 : ℝ) < M.lam j + δ2 / n := by
      have := M.hlam_pos j; have := M.hδ2; positivity
    exact hlim.eventually (eventually_gt_nhds hpos)
  have hpar := floor_parallel M hFact1 hFact2n hFact3n hFact2k hFact3k j
  -- Claim 2a: eventual equality of `sinSq`.
  have hclaim2a : ∀ᶠ P : Adm k in atTop,
      sinSq (Matrix.toEuclideanLin (M.b P)ᵀ (M.h P j)) ej = sinSq (uP P) ej := by
    filter_upwards [hpar, hθpos] with P ⟨c, hc⟩ hθpos
    set p : ℝ := (P.1 : ℝ) with hpdef
    have hp : (0 : ℝ) < p := by
      have : (0 : ℕ) < P.1 := lt_of_lt_of_le M.hk P.2
      rw [hpdef]; exact_mod_cast this
    have hsp : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hp
    have hsp_ne : Real.sqrt p ≠ 0 := ne_of_gt hsp
    have hsqrt : Real.sqrt p * (1 / Real.sqrt p) = 1 := by
      field_simp
    -- c ≠ 0 : else h P j = 0 contradicting unit norm.
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hz : M.h P j = 0 := by rw [hc, hc0, zero_smul]
      have hu := M.hh_unit P j
      rw [hz, norm_zero] at hu
      norm_num at hu
    -- Rewrite `bᵀ (h P j)` via `hc`.
    have hb1 : Matrix.toEuclideanLin (M.b P)ᵀ (M.h P j)
        = c • Matrix.toEuclideanLin ((M.b P)ᵀ * Ymat M P) (M.w P j) := by
      rw [hc, map_smul, toEuclideanLin_comp]
    -- `(b)ᵀ * Ymat = Φ + bᵀ Z`.
    have hmatid : (M.b P)ᵀ * Ymat M P = M.Φ P + (M.b P)ᵀ * M.Z P := by
      rw [Ymat, Matrix.mul_add, ← Matrix.mul_assoc, M.hb_ortho P, Matrix.one_mul]
    -- `Φ + bᵀ Z = √p • ((1/√p)•Φ + (1/√p)•(bᵀZ))`.
    have hscale : M.Φ P + (M.b P)ᵀ * M.Z P
        = Real.sqrt p • (((1 / Real.sqrt p) • M.Φ P)
            + ((1 / Real.sqrt p) • ((M.b P)ᵀ * M.Z P))) := by
      rw [smul_add, smul_smul, smul_smul, hsqrt, one_smul, one_smul]
    rw [hmatid, hscale, map_smul, LinearMap.smul_apply] at hb1
    -- Now `bᵀ (h P j) = (c * √p) • uP P`.
    have hb2 : Matrix.toEuclideanLin (M.b P)ᵀ (M.h P j) = (c * Real.sqrt p) • uP P := by
      rw [hb1, smul_smul, huP, hpdef]
    rw [hb2, sinSq_smul_left _ (mul_ne_zero hc_ne hsp_ne)]
  -- Claim 2b: `uP → L • νn j`.
  -- The matrix argument converges to `Φbarinf + 0`.
  have hA : Tendsto
      (fun P : Adm k => ((1 / Real.sqrt P.1) • M.Φ P)
          + ((1 / Real.sqrt P.1) • ((M.b P)ᵀ * M.Z P)))
      atTop (𝓝 (M.Φbarinf + 0)) :=
    (M.field3_signalLimit).add (M.field2_decoherence)
  -- `w P j → wn j`.
  have hw := M.field5_dualEigvec j
  -- tendsto of `toEuclideanLin (A P) (v P)` via `toLp (A *ᵥ ofLp v)`.
  have hcont : Continuous
      (fun q : Matrix (Fin k) (Fin n) ℝ × EuclideanSpace ℝ (Fin n) =>
        (WithLp.toLp 2 (q.1 *ᵥ WithLp.ofLp q.2) : EuclideanSpace ℝ (Fin k))) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).comp
    exact (continuous_fst.matrix_mulVec
      ((PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).comp continuous_snd))
  have hpair : Tendsto
      (fun P : Adm k => (((1 / Real.sqrt P.1) • M.Φ P)
          + ((1 / Real.sqrt P.1) • ((M.b P)ᵀ * M.Z P)), M.w P j))
      atTop (𝓝 (M.Φbarinf + 0, M.wn j)) :=
    hA.prodMk_nhds hw
  have huPlim : Tendsto uP atTop
      (𝓝 (Matrix.toEuclideanLin (M.Φbarinf + 0) (M.wn j))) := by
    have hc := (hcont.tendsto _).comp hpair
    have hfun : uP = fun P => WithLp.toLp 2
        ((((1 / Real.sqrt P.1) • M.Φ P) + ((1 / Real.sqrt P.1) • ((M.b P)ᵀ * M.Z P)))
          *ᵥ WithLp.ofLp (M.w P j)) := by
      funext P; simp only [huP, Matrix.toEuclideanLin_apply]
    rw [hfun, Matrix.toEuclideanLin_apply]
    exact hc
  -- The limit equals `L • νn j`.
  have hlimval : Matrix.toEuclideanLin (M.Φbarinf + 0) (M.wn j) = L • M.νn j := by
    rw [add_zero, M.field6_duality j, hLdef]
  rw [hlimval] at huPlim
  -- Step 3: assemble.
  have hlim := sinSq_tendsto' (u := L • M.νn j) (v := ej) hLνn_ne hej_ne
    huPlim (tendsto_const_nhds (x := ej))
  refine hlim.congr' ?_
  filter_upwards [hclaim2a] with P hP
  rw [hP]

/-- **Statement 1 (Theorem 1 — error decomposition).** Given an instance of the
bundle and the Facts at dimensions `n` and `k`: for each `j`, as `p → ∞`,
`sin²∠(hⱼ, bⱼ) → δ²/(n λⱼ^{(n)} + δ²) + (n λⱼ^{(n)}/(n λⱼ^{(n)} + δ²)) ·
sin²∠(νⱼ^{(n)}, eⱼ)`, the out-of-subspace floor plus the in-subspace rotation. -/
theorem theorem1_error_decomposition {k n : ℕ} {δ2 : ℝ}
    (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) :
    ∀ j : Fin k,
      Tendsto (fun P : Adm k => sinSq (M.h P j) (colVec (M.b P) j)) atTop
        (𝓝 (δ2 / ((n : ℝ) * M.lam j + δ2)
            + ((n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2))
              * sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ)))) := by
  intro j
  have hfloor := floor_limit M hFact1 hFact2n hFact3n hFact2k hFact3k j
  -- Finite-p pointwise identity (★): rewrite sinSq(hⱼ,bⱼ) as floor + rotation part.
  -- Notation: cⱼ := bᵀ hⱼ ∈ ℝ^k  (the projected/dual coordinates of hⱼ).
  set cvec : Adm k → EuclideanSpace ℝ (Fin k) :=
    fun P => Matrix.toEuclideanLin (M.b P)ᵀ (M.h P j) with hcvec
  -- (★) finite-p pointwise identity: sin²∠(hⱼ,bⱼ) = ‖Π⊥ hⱼ‖² + ‖cⱼ‖²·sin²∠(cⱼ,eⱼ).
  -- Proof (Pythagoras + b isometry): ⟨hⱼ,bⱼ⟩ = ⟨cⱼ, eⱼ⟩ (b isometry, bⱼ = b·eⱼ),
  -- ‖Π hⱼ‖² = ‖cⱼ‖², 1 = ‖Π hⱼ‖² + ‖Π⊥ hⱼ‖²; then expand sinSq defs.
  have hstar : ∀ P : Adm k,
      sinSq (M.h P j) (colVec (M.b P) j)
        = ‖Matrix.toEuclideanLin (1 - M.b P * (M.b P)ᵀ) (M.h P j)‖ ^ 2
          + ‖cvec P‖ ^ 2 * sinSq (cvec P) (EuclideanSpace.single j (1 : ℝ)) := by
    intro P
    set b := M.b P with hb_def
    set hj := M.h P j with hj_def
    set ej : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single j (1 : ℝ) with hej
    have hbortho : bᵀ * b = 1 := M.hb_ortho P
    have hhunit : ‖hj‖ = 1 := M.hh_unit P j
    -- `bj = toEuclideanLin b ej`
    have hbj : colVec b j = Matrix.toEuclideanLin b ej := colVec_eq_toEuclideanLin b j
    -- `‖ej‖ = 1`
    have hej_norm : ‖ej‖ = 1 := by
      rw [hej, EuclideanSpace.norm_single]; norm_num
    -- `‖bj‖ = 1`
    have hbj_norm : ‖colVec b j‖ = 1 := by
      rw [hbj, norm_toEuclideanLin_ortho b hbortho, hej_norm]
    -- adjoint identity: ⟨hj, toEuclideanLin b y⟩ = ⟨toEuclideanLin bᵀ hj, y⟩
    have hadj : ∀ y : EuclideanSpace ℝ (Fin k),
        (inner ℝ hj (Matrix.toEuclideanLin b y) : ℝ)
          = inner ℝ (Matrix.toEuclideanLin bᵀ hj) y := by
      intro y
      rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
      rw [Matrix.piLp_ofLp_toEuclideanLin, Matrix.piLp_ofLp_toEuclideanLin]
      simp only [Matrix.toLin'_apply, star_trivial]
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    -- ⟨hj, bj⟩ = ⟨cⱼ, eⱼ⟩
    have hinner_eq : (inner ℝ hj (colVec b j) : ℝ) = inner ℝ (cvec P) ej := by
      rw [hbj, hadj ej, hcvec]
    -- step 2: sinSq hj bj = 1 - ⟨hj,bj⟩²
    have hstep2 : sinSq hj (colVec b j) = 1 - (inner ℝ hj (colVec b j) : ℝ) ^ 2 :=
      sinSq_of_unit hhunit hbj_norm
    -- Π hj = toEuclideanLin (b*bᵀ) hj = toEuclideanLin b (cvec P)
    have hProj : Matrix.toEuclideanLin (b * bᵀ) hj
        = Matrix.toEuclideanLin b (cvec P) := by
      rw [hcvec, toEuclideanLin_comp]
    -- ‖Π hj‖ = ‖cⱼ‖
    have hPnorm : ‖Matrix.toEuclideanLin (b * bᵀ) hj‖ = ‖cvec P‖ := by
      rw [hProj, norm_toEuclideanLin_ortho b hbortho]
    -- decompose Π⊥ hj = hj - Π hj
    have hsplit : Matrix.toEuclideanLin (1 - b * bᵀ) hj
        = hj - Matrix.toEuclideanLin (b * bᵀ) hj := by
      ext i
      simp only [Matrix.toEuclideanLin_apply, PiLp.sub_apply, Matrix.sub_mulVec,
        Matrix.one_mulVec, Pi.sub_apply]
    -- ⟨hj, Π hj⟩ = ‖cⱼ‖²
    have hinner_proj : (inner ℝ hj (Matrix.toEuclideanLin (b * bᵀ) hj) : ℝ)
        = ‖cvec P‖ ^ 2 := by
      rw [hProj, hadj (cvec P), hcvec, real_inner_self_eq_norm_sq]
    -- ‖Π⊥ hj‖² = 1 - ‖cⱼ‖²
    have hPerp : ‖Matrix.toEuclideanLin (1 - b * bᵀ) hj‖ ^ 2 = 1 - ‖cvec P‖ ^ 2 := by
      rw [hsplit, ← real_inner_self_eq_norm_sq]
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      rw [real_inner_self_eq_norm_sq, hhunit]
      rw [real_inner_self_eq_norm_sq, hPnorm]
      have hcross : (inner ℝ (Matrix.toEuclideanLin (b * bᵀ) hj) hj : ℝ) = ‖cvec P‖ ^ 2 := by
        rw [real_inner_comm, hinner_proj]
      rw [hcross, hinner_proj]
      ring
    -- rotation term: ‖cⱼ‖² * sinSq cⱼ eⱼ = ‖cⱼ‖² - ⟨cⱼ, eⱼ⟩²
    have hrot_eq : ‖cvec P‖ ^ 2 * sinSq (cvec P) ej
        = ‖cvec P‖ ^ 2 - (inner ℝ (cvec P) ej : ℝ) ^ 2 := by
      unfold sinSq
      rw [hej_norm]
      by_cases hc0 : ‖cvec P‖ = 0
      · rw [hc0]
        have hz : cvec P = 0 := by rwa [norm_eq_zero] at hc0
        rw [hz]; simp
      · have hc2 : ‖cvec P‖ ^ 2 ≠ 0 := pow_ne_zero 2 hc0
        field_simp
    show sinSq hj (colVec b j)
        = ‖Matrix.toEuclideanLin (1 - b * bᵀ) hj‖ ^ 2
          + ‖cvec P‖ ^ 2 * sinSq (cvec P) ej
    rw [hstep2, hinner_eq, hPerp, hrot_eq]
    ring
  -- rotation limit: ‖cⱼ‖²·sin²∠(cⱼ,eⱼ) → (nλⱼ/(nλⱼ+δ²))·sin²∠(νⱼ,eⱼ).
  have hrot : Tendsto
      (fun P : Adm k => ‖cvec P‖ ^ 2 * sinSq (cvec P) (EuclideanSpace.single j (1 : ℝ)))
      atTop
      (𝓝 (((n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2))
            * sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ)))) := by
    have h1 := cvec_normSq_limit M hFact1 hFact2n hFact3n hFact2k hFact3k j
    have h2 := cvec_sinSq_limit M hFact1 hFact2n hFact3n hFact2k hFact3k j
    simp only [hcvec]
    exact h1.mul h2
  refine (hfloor.add hrot).congr' ?_
  filter_upwards with P
  exact (hstar P).symm

/-- **Statement 2 (Corollary 1 — observable floor).** Under the same hypotheses,
for each `j`, as `p → ∞`:
(1) `ℓ^{(p,n)} → δ²/n`;
(2) `θⱼ^{(p,n)} → λⱼ^{(n)} + δ²/n`, and this limit is positive;
(3) `sin²∠(hⱼ, col(B)) := ‖Π⊥ hⱼ‖² → δ²/(n λⱼ^{(n)} + δ²)` (with `Π⊥ = I − b bᵀ`);
(4) `ℓ^{(p,n)}/θⱼ^{(p,n)} → δ²/(n λⱼ^{(n)} + δ²)`, equal to the floor of (3);
(5) this limiting ratio is `≤` the Theorem 1 limit, with equality iff
    `sin²∠(νⱼ^{(n)}, eⱼ) = 0`. -/
theorem corollary1_observable_floor {k n : ℕ} {δ2 : ℝ}
    (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) :
    ∀ j : Fin k,
      -- (1) trailing (bulk) average limit
      (Tendsto (fun P : Adm k => (1 / ((n : ℝ) - k)) *
          ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), M.θ P i)
          atTop (𝓝 (δ2 / n))) ∧
      -- (2) dual eigenvalue limit, positive
      (Tendsto (fun P : Adm k => M.θ P (Fin.castLE (le_of_lt M.hkn) j)) atTop
          (𝓝 (M.lam j + δ2 / n)) ∧ 0 < M.lam j + δ2 / n) ∧
      -- (3) angle to the column space col(B) = col(b)
      (Tendsto
          (fun P : Adm k =>
            ‖Matrix.toEuclideanLin (1 - (M.b P) * (M.b P)ᵀ) (M.h P j)‖ ^ 2)
          atTop (𝓝 (δ2 / ((n : ℝ) * M.lam j + δ2)))) ∧
      -- (4) observable ratio limit, equal to the floor
      (Tendsto
          (fun P : Adm k => ((1 / ((n : ℝ) - k)) *
              ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ (i : ℕ)), M.θ P i)
            / M.θ P (Fin.castLE (le_of_lt M.hkn) j)) atTop
          (𝓝 (δ2 / ((n : ℝ) * M.lam j + δ2)))) ∧
      -- (5) the ratio is ≤ the Theorem 1 limit, with equality iff the rotation vanishes
      (δ2 / ((n : ℝ) * M.lam j + δ2)
          ≤ δ2 / ((n : ℝ) * M.lam j + δ2)
            + ((n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2))
              * sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ))) ∧
      (δ2 / ((n : ℝ) * M.lam j + δ2)
          = δ2 / ((n : ℝ) * M.lam j + δ2)
            + ((n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2))
              * sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ))
        ↔ sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ)) = 0) := by
  intro j
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- (1) trailing (bulk) average limit `ℓ^{(p,n)} → δ²/n`.
    exact M.field4_trailing
  · -- (2a) dual eigenvalue limit `θⱼ^{(p,n)} → λⱼ^{(n)} + δ²/n`.
    exact M.field4_dualSpectrum j
  · -- (2b) positivity `0 < λⱼ^{(n)} + δ²/n`.
    -- `M.hlam_pos j : 0 < λⱼ`, `M.hδ2 : 0 < δ²`, `n > 0` (from hk,hkn).
    have hn : (0 : ℝ) < n := by
      have : (0 : ℕ) < n := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
      exact_mod_cast this
    have := M.hlam_pos j
    have := M.hδ2
    positivity
  · -- (3) `‖Π⊥ hⱼ‖² → δ²/(n λⱼ + δ²)`.  This is exactly the shared floor lemma.
    exact floor_limit M hFact1 hFact2n hFact3n hFact2k hFact3k j
  · -- (4) observable ratio `ℓ^{(p,n)}/θⱼ^{(p,n)} → δ²/(n λⱼ + δ²)`.
    -- `ℓ → δ²/n` (field4_trailing), `θⱼ → λⱼ + δ²/n` with limit ≠ 0 (part 2).
    -- `Tendsto.div` gives `ℓ/θⱼ → (δ²/n)/(λⱼ+δ²/n)`; then `field_simp`/`ring`
    -- normalizes `(δ²/n)/(λⱼ+δ²/n) = δ²/(nλⱼ+δ²)` using `n > 0`, `nλⱼ+δ² ≠ 0`.
    have hn : (0 : ℝ) < n := by
      have : (0 : ℕ) < n := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
      exact_mod_cast this
    have hlam := M.hlam_pos j
    have hδ := M.hδ2
    have hden : M.lam j + δ2 / n ≠ 0 := by positivity
    have hden2 : (n : ℝ) * M.lam j + δ2 ≠ 0 := by positivity
    have hdiv := M.field4_trailing.div (M.field4_dualSpectrum j) hden
    convert hdiv using 2
    field_simp
  · -- (5a) inequality `δ²/(nλⱼ+δ²) ≤ δ²/(nλⱼ+δ²) + coeff·sin²∠(νⱼ,eⱼ)`.
    -- Reduces to `0 ≤ coeff·sin²∠(νⱼ,eⱼ)`.  `coeff = nλⱼ/(nλⱼ+δ²) ≥ 0`
    -- (n>0, λⱼ>0, δ²>0), and `sin²∠ ≥ 0` (`sinSq_nonneg_unit` with hνn_unit, and
    -- ‖eⱼ‖=1 = `EuclideanSpace.norm_single`).  `le_add_of_nonneg_right`; then
    -- `positivity`/`mul_nonneg`.
    have hn : (0 : ℝ) < n := by
      have : (0 : ℕ) < n := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
      exact_mod_cast this
    have hlam := M.hlam_pos j
    have hδ := M.hδ2
    have hsin : 0 ≤ sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ)) := by
      apply sinSq_nonneg_unit (M.hνn_unit j)
      simp
    have hcoeff : 0 ≤ (n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2) := by positivity
    exact le_add_of_nonneg_right (mul_nonneg hcoeff hsin)
  · -- (5b) equality iff `sin²∠(νⱼ,eⱼ) = 0`.
    -- Equation is `x = x + coeff·s ↔ coeff·s = 0`.  Since `coeff > 0` (strict:
    -- n>0, λⱼ>0, nλⱼ+δ²>0), `coeff·s = 0 ↔ s = 0` (`mul_eq_zero`, coeff ≠ 0).
    have hn : (0 : ℝ) < n := by
      have : (0 : ℕ) < n := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one M.hk) (le_of_lt M.hkn)
      exact_mod_cast this
    have hlam := M.hlam_pos j
    have hδ := M.hδ2
    have hcoeff_pos : 0 < (n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2) := by positivity
    constructor
    · intro h
      have hzero : (n : ℝ) * M.lam j / ((n : ℝ) * M.lam j + δ2) *
          sinSq (M.νn j) (EuclideanSpace.single j (1 : ℝ)) = 0 := by linarith
      rcases mul_eq_zero.mp hzero with h1 | h2
      · exact absurd h1 (ne_of_gt hcoeff_pos)
      · exact h2
    · intro h; rw [h, mul_zero, add_zero]

/-- **Statement 3 (Corollary 2 — subspace error).** With `H := [h₁ ⋯ h_k]`,
`P_H := H Hᵀ`, `P_B := b bᵀ`: at every admissible `p` the Frobenius identity
`(1/2)‖P_H − P_B‖_F² = Σⱼ sin²∠(hⱼ, col(B))` holds (using that both `H` and `b`
have `k` orthonormal columns), and as `p → ∞`,
`(1/2)‖P_H − P_B‖_F² → Σⱼ δ²/(n λⱼ^{(n)} + δ²)`. -/
theorem corollary2_subspace_error {k n : ℕ} {δ2 : ℝ}
    (M : AsymptoticModel k n δ2)
    (hFact1 : Fact1_SLLN) (hFact2n : Fact2_Weyl n) (hFact3n : Fact3_EigCont n)
    (hFact2k : Fact2_Weyl k) (hFact3k : Fact3_EigCont k) :
    -- finite-`p` Frobenius identity (at every admissible `p`)
    (∀ P : Adm k,
      (1 / 2 : ℝ) * frobSq ((Hmat (M.h P)) * (Hmat (M.h P))ᵀ - (M.b P) * (M.b P)ᵀ)
        = ∑ j : Fin k,
            ‖Matrix.toEuclideanLin (1 - (M.b P) * (M.b P)ᵀ) (M.h P j)‖ ^ 2) ∧
    -- asymptotic limit
    Tendsto
      (fun P : Adm k => (1 / 2 : ℝ) *
        frobSq ((Hmat (M.h P)) * (Hmat (M.h P))ᵀ - (M.b P) * (M.b P)ᵀ)) atTop
      (𝓝 (∑ j : Fin k, δ2 / ((n : ℝ) * M.lam j + δ2))) := by
  -- Shared finite-p Frobenius identity.
  have hid : ∀ P : Adm k,
      (1 / 2 : ℝ) * frobSq ((Hmat (M.h P)) * (Hmat (M.h P))ᵀ - (M.b P) * (M.b P)ᵀ)
        = ∑ j : Fin k,
            ‖Matrix.toEuclideanLin (1 - (M.b P) * (M.b P)ᵀ) (M.h P j)‖ ^ 2 := by
    intro P
    -- Let P_H = H Hᵀ, P_B = b bᵀ.  Both H and b have k orthonormal columns
    -- (`hH_ortho`, `hb_ortho`), so P_H, P_B are orthogonal projectors of rank k.
    -- ½‖P_H − P_B‖_F² = k − tr(P_H P_B) = Σⱼ ‖Π⊥ hⱼ‖².
    set b := M.b P with hbdef
    set hh := M.h P with hhdef
    have hbo : bᵀ * b = 1 := M.hb_ortho P
    have hHo : (Hmat hh)ᵀ * (Hmat hh) = 1 := M.hH_ortho P
    set H := Hmat hh with hHdef
    set PH := H * Hᵀ with hPHdef
    set PB := b * bᵀ with hPBdef
    -- frobSq = trace
    have frob_trace : ∀ {r s : ℕ} (D : Matrix (Fin r) (Fin s) ℝ),
        frobSq D = (Dᵀ * D).trace := by
      intro r s D
      simp only [frobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.transpose_apply, sq]
      rw [Finset.sum_comm]
    -- symmetry
    have hPHsymm : PHᵀ = PH := by
      rw [hPHdef, Matrix.transpose_mul, Matrix.transpose_transpose]
    have hPBsymm : PBᵀ = PB := by
      rw [hPBdef, Matrix.transpose_mul, Matrix.transpose_transpose]
    -- idempotence
    have hPHidem : PH * PH = PH := by
      rw [hPHdef, Matrix.mul_assoc, ← Matrix.mul_assoc Hᵀ H Hᵀ, hHo, Matrix.one_mul]
    have hPBidem : PB * PB = PB := by
      rw [hPBdef, Matrix.mul_assoc, ← Matrix.mul_assoc bᵀ b bᵀ, hbo, Matrix.one_mul]
    -- traces
    have htrPH : PH.trace = (k : ℝ) := by
      rw [hPHdef, Matrix.trace_mul_comm, hHo, Matrix.trace_one]; simp
    have htrPB : PB.trace = (k : ℝ) := by
      rw [hPBdef, Matrix.trace_mul_comm, hbo, Matrix.trace_one]; simp
    -- LHS = k - tr(P_H P_B)
    have hLHS : (1 / 2 : ℝ) * frobSq (PH - PB) = (k : ℝ) - (PH * PB).trace := by
      rw [frob_trace]
      have hD : (PH - PB)ᵀ = PH - PB := by
        rw [Matrix.transpose_sub, hPHsymm, hPBsymm]
      rw [hD]
      have hexpand : (PH - PB) * (PH - PB)
          = PH * PH - PH * PB - PB * PH + PB * PB := by
        rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]; abel
      rw [hexpand, hPHidem, hPBidem]
      rw [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
      have hcyc : (PB * PH).trace = (PH * PB).trace := Matrix.trace_mul_comm PB PH
      rw [hcyc, htrPH, htrPB]; ring
    -- RHS = k - tr(P_H P_B)
    have hRHS : (∑ j : Fin k, ‖Matrix.toEuclideanLin (1 - PB) (hh j)‖ ^ 2)
        = (k : ℝ) - (PH * PB).trace := by
      have hcol : ∀ j : Fin k, ‖Matrix.toEuclideanLin (1 - PB) (hh j)‖ ^ 2
          = (((1 - PB) * H)ᵀ * ((1 - PB) * H) : Matrix (Fin k) (Fin k) ℝ) j j := by
        intro j
        rw [EuclideanSpace.norm_sq_eq, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        have hc : ((1 - PB) * H : Matrix (Fin P.1) (Fin k) ℝ) i j
            = (Matrix.toEuclideanLin (1 - PB) (hh j)) i := by
          rw [Matrix.toEuclideanLin_apply]
          simp only [hHdef, Hmat, Matrix.mulVec, Matrix.mul_apply, Matrix.of_apply]
          rfl
        rw [Matrix.transpose_apply, hc, Real.norm_eq_abs, sq_abs, sq]
      simp_rw [hcol]
      have hsum : (∑ j : Fin k,
            (((1 - PB) * H)ᵀ * ((1 - PB) * H) : Matrix (Fin k) (Fin k) ℝ) j j)
          = (((1 - PB) * H)ᵀ * ((1 - PB) * H)).trace := rfl
      rw [hsum]
      have hCsymm : (1 - PB)ᵀ = 1 - PB := by
        rw [Matrix.transpose_sub, Matrix.transpose_one, hPBsymm]
      have hCidem : (1 - PB) * (1 - PB) = 1 - PB := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPBidem]
        abel
      rw [Matrix.transpose_mul, hCsymm]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - PB) (1 - PB) H, hCidem]
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.trace_sub]
      have h1 : (Hᵀ * H).trace = (k : ℝ) := by rw [hHo, Matrix.trace_one]; simp
      have h2 : (Hᵀ * (PB * H)).trace = (PH * PB).trace := by
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (Hᵀ * PB) H,
          ← Matrix.mul_assoc, hPHdef,
          Matrix.trace_mul_comm (H * Hᵀ) PB, Matrix.trace_mul_comm PB PH, hPHdef]
      rw [h1, h2]
    rw [hLHS, hRHS]
  refine ⟨hid, ?_⟩
  -- Asymptotic limit `½‖P_H − P_B‖_F² → Σⱼ δ²/(nλⱼ+δ²)`.
  -- By the finite-p identity (`hid`), the LHS equals `Σⱼ ‖Π⊥ hⱼ‖²` for every P,
  -- and each summand tends to `δ²/(nλⱼ+δ²)` by `floor_limit`.
  refine Tendsto.congr (fun P => (hid P).symm) ?_
  exact tendsto_finset_sum _
    (fun j _ => floor_limit M hFact1 hFact2n hFact3n hFact2k hFact3k j)

/-- **Statement 4 (Corollary 3 — noiseless case, exact at finite `p`; STANDALONE).**
A finite-`p` linear-algebra identity with its own minimal hypotheses. Fix
`1 ≤ k < n` and `k < p`; orthonormal `b`, arbitrary `Φ`,
`S⁰ := b Φ Φᵀ bᵀ/(np)`, `N := Φ Φᵀ/(np)`; an index `j` and a value `μⱼ` that is a
simple eigenvalue of both `S⁰` and `N`, with unit eigenvectors `h⁰ⱼ` (of `S⁰`) and
`νⱼ` (of `N`) at `μⱼ`. Then `sin²∠(h⁰ⱼ, bⱼ) = sin²∠(νⱼ, eⱼ)`. -/
theorem corollary3_noiseless {p k n : ℕ}
    (hk : 1 ≤ k) (hkn : k < n) (hkp : k < p)
    (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (Φ : Matrix (Fin k) (Fin n) ℝ)
    (S0 : Matrix (Fin p) (Fin p) ℝ)
    (hS0 : S0 = (1 / ((n : ℝ) * p)) • (b * Φ * Φᵀ * bᵀ))
    (Npn : Matrix (Fin k) (Fin k) ℝ)
    (hNpn : Npn = (1 / ((n : ℝ) * p)) • (Φ * Φᵀ))
    (j : Fin k) (μj : ℝ)
    (h0j : EuclideanSpace ℝ (Fin p)) (νj : EuclideanSpace ℝ (Fin k))
    -- `μⱼ` a simple eigenvalue of `S⁰` with unit eigenvector `h⁰ⱼ`
    (hh0j_unit : ‖h0j‖ = 1)
    (hh0j_eig : Matrix.toEuclideanLin S0 h0j = μj • h0j)
    (hh0j_simple : ∀ w : EuclideanSpace ℝ (Fin p), ‖w‖ = 1 →
      Matrix.toEuclideanLin S0 w = μj • w → w = h0j ∨ w = -h0j)
    -- `μⱼ` a simple eigenvalue of `N^{(p,n)}` with unit eigenvector `νⱼ`
    (hνj_unit : ‖νj‖ = 1)
    (hνj_eig : Matrix.toEuclideanLin Npn νj = μj • νj)
    (hνj_simple : ∀ w : EuclideanSpace ℝ (Fin k), ‖w‖ = 1 →
      Matrix.toEuclideanLin Npn w = μj • w → w = νj ∨ w = -νj)
    (hFact1 : Fact1_SLLN) (hFact2p : Fact2_Weyl p) (hFact3p : Fact3_EigCont p) :
    sinSq h0j (colVec b j) = sinSq νj (EuclideanSpace.single j (1 : ℝ)) := by
  -- key matrix identity: S0 * b = b * Npn
  have hSb : S0 * b = b * Npn := by
    rw [hS0, hNpn, Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    have : (b * Φ * Φᵀ * bᵀ) * b = b * Φ * Φᵀ * (bᵀ * b) := by
      simp [Matrix.mul_assoc]
    rw [this, hb]
    simp [Matrix.mul_assoc]
  -- v := toEuclideanLin b νj is a unit eigenvector of S0 at μj
  set v : EuclideanSpace ℝ (Fin p) := Matrix.toEuclideanLin b νj with hv
  have hv_unit : ‖v‖ = 1 := by rw [hv, norm_toEuclideanLin_ortho b hb, hνj_unit]
  have hv_eig : Matrix.toEuclideanLin S0 v = μj • v := by
    apply WithLp.ofLp_injective
    rw [Matrix.piLp_ofLp_toEuclideanLin]
    simp only [Matrix.toLin'_apply]
    rw [hv, Matrix.piLp_ofLp_toEuclideanLin]
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, hSb, ← Matrix.mulVec_mulVec]
    have : Npn *ᵥ WithLp.ofLp νj = WithLp.ofLp (μj • νj) := by
      rw [← Matrix.toLin'_apply, ← Matrix.piLp_ofLp_toEuclideanLin, hνj_eig]
    rw [this]
    rw [WithLp.ofLp_smul, Matrix.mulVec_smul]
    simp [WithLp.ofLp_smul]
  -- simplicity: h0j = ± v
  have hcase := hh0j_simple v hv_unit hv_eig
  -- inner products
  have hcol : colVec b j = Matrix.toEuclideanLin b (EuclideanSpace.single j (1:ℝ)) :=
    colVec_eq_toEuclideanLin b j
  have hinner : (inner ℝ v (colVec b j) : ℝ)
      = inner ℝ νj (EuclideanSpace.single j (1:ℝ)) := by
    rw [hv, hcol, inner_toEuclideanLin_ortho b hb]
  have hnorm_col : ‖colVec b j‖ = ‖(EuclideanSpace.single j (1:ℝ))‖ := by
    rw [hcol, norm_toEuclideanLin_ortho b hb]
  -- final computation of sinSq
  have key : sinSq h0j (colVec b j) = sinSq v (colVec b j) := by
    rcases hcase with h | h
    · rw [h]
    · rw [h]; simp only [sinSq, inner_neg_left, norm_neg]; ring_nf
  rw [key]
  simp only [sinSq]
  rw [hinner, hv_unit, hnorm_col, hνj_unit]

end

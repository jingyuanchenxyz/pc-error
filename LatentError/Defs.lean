import Mathlib
import LatentError.Basic

/-!
# Shared definitions for "Principal component error in high-dimensional factor models"

Numbering follows the *current* paper (Bernstein–Goldberg–Gunther–Kercheval–Lan–Lin–Yao,
version of Sept 14, 2026), not the early preprint used by the AxiomProver formalization
in `LatentError/Ono/Solution.lean`.  From that formalization we reuse (via
`LatentError/Basic.lean`) only `sinSq`, `colVec`, `opNorm`, `frobSq`, `Hmat` and the
three facts `Fact1_SLLN`, `Fact2_Weyl`, `Fact3_EigCont`.

Everything is indexed by the *actual* cross-section size `p : ℕ`; objects that only make
sense for `k ≤ p` are required to behave only eventually (`∀ᶠ p in atTop`).
-/

open scoped Matrix Topology MatrixOrder
open Filter

noncomputable section

namespace PCError

variable {k n : ℕ}

/-! ## Spectral vocabulary -/

open Classical in
/-- The `j`-th largest eigenvalue (0-indexed, weakly decreasing order) of a real square
matrix; `0` if the matrix is not symmetric. -/
def sortedEig {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (j : Fin m) : ℝ :=
  if h : A.IsHermitian then h.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm j) else 0

/-- `sortedEig` with a natural-number index, padded by `0` beyond the size.  With this
padding, Gram duality reads `sortedEigN (A Aᵀ) = sortedEigN (Aᵀ A)` (Lemma 1). -/
def sortedEigN {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (j : ℕ) : ℝ :=
  if h : j < m then sortedEig A ⟨j, h⟩ else 0

/-- `v` is a unit eigenvector of `A` with eigenvalue `μ`. -/
def IsUnitEigvec {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (v : EuclideanSpace ℝ (Fin m))
    (μ : ℝ) : Prop :=
  ‖v‖ = 1 ∧ Matrix.toEuclideanLin A v = μ • v

/-- `V` is an orthogonal eigenbasis of `K`, columns in decreasing eigenvalue order. -/
def IsEigenbasis (K V : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  Vᵀ * V = 1 ∧ K * V = V * Matrix.diagonal (sortedEig K)

/-- The standard basis vector `eⱼ ∈ ℝᵏ`. -/
abbrev e (j : Fin k) : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single j (1 : ℝ)

/-! ## Angles to subspaces (eq. (10)) -/

/-- The orthogonal projector `Π = b bᵀ` onto `col(b)` (for `bᵀ b = I`). -/
def projB {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) : Matrix (Fin p) (Fin p) ℝ := b * bᵀ

/-- `sin²∠(u, col b) = 1 − ‖Π u‖² / ‖u‖²` with `Π = b bᵀ` (eq. (10)). -/
def sinSqSub {p : ℕ} (u : EuclideanSpace ℝ (Fin p)) (b : Matrix (Fin p) (Fin k) ℝ) : ℝ :=
  1 - ‖Matrix.toEuclideanLin (projB b) u‖ ^ 2 / ‖u‖ ^ 2

/-- `b` is a principal frame of the population matrix `Σ₀`: orthonormal columns, and
column `j` is an eigenvector of `Σ₀` for its `j`-th largest eigenvalue (eq. (3)). -/
def IsPrincipalFrame {p : ℕ} (Sig0 : Matrix (Fin p) (Fin p) ℝ)
    (b : Matrix (Fin p) (Fin k) ℝ) : Prop :=
  bᵀ * b = 1 ∧ ∀ j : Fin k,
    Matrix.toEuclideanLin Sig0 (colVec b j) = sortedEigN Sig0 j • colVec b j

/-! ## Model matrices -/

/-- The first `p` rows of an infinite array with `c` columns (the nesting convention of
Section 4, used for both the loadings `B` and the noise `Z`). -/
def truncRows {c : ℕ} (A : ℕ → Fin c → ℝ) (p : ℕ) : Matrix (Fin p) (Fin c) ℝ :=
  Matrix.of fun i j => A i j

/-- Loadings `B⁽ᵖ⁾ ∈ ℝ^{p×k}`. -/
abbrev Bmat (Barr : ℕ → Fin k → ℝ) (p : ℕ) : Matrix (Fin p) (Fin k) ℝ := truncRows Barr p

/-- `G_B⁽ᵖ⁾ = BᵀB/p`. -/
def GBp (Barr : ℕ → Fin k → ℝ) (p : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  (1 / (p : ℝ)) • ((Bmat Barr p)ᵀ * Bmat Barr p)

/-- Population systematic covariance `Σ₀ = B Σ_f Bᵀ` (eq. (2)). -/
def Sig0 (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Bmat Barr p * Sf * (Bmat Barr p)ᵀ

/-- `K(Σ) = Σ^{1/2} G Σ^{1/2}` (Assumption 5, Appendix B). -/
def Kmat (Sf G : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt Sf * G * CFC.sqrt Sf

/-- Data matrix `Y = B F + Z ∈ ℝ^{p×n}` (eqs. (7), (42)); `Zarr i l = Z_{il}`. -/
def Ymat (Barr : ℕ → Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ) (Zarr : ℕ → Fin n → ℝ)
    (p : ℕ) : Matrix (Fin p) (Fin n) ℝ :=
  Bmat Barr p * F + truncRows Zarr p

/-- Scaled sample covariance `S⁽ᵖ⁾ = Y Yᵀ/(np)` (eq. (8)). -/
def Scov (Barr : ℕ → Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ) (Zarr : ℕ → Fin n → ℝ)
    (p : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
  (1 / ((n : ℝ) * p)) • (Ymat Barr F Zarr p * (Ymat Barr F Zarr p)ᵀ)

/-- Dual `W⁽ᵖ⁾ = YᵀY/(np)` (eq. (11)). -/
def Wdual (Barr : ℕ → Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ) (Zarr : ℕ → Fin n → ℝ)
    (p : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (1 / ((n : ℝ) * p)) • ((Ymat Barr F Zarr p)ᵀ * Ymat Barr F Zarr p)

/-- `θᵢ⁽ᵖ⁾`, the `i`-th largest eigenvalue of `W⁽ᵖ⁾`. -/
def theta (Barr : ℕ → Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ) (Zarr : ℕ → Fin n → ℝ)
    (p : ℕ) (i : ℕ) : ℝ :=
  sortedEigN (Wdual Barr F Zarr p) i

/-- Average bulk eigenvalue `ℓ⁽ᵖ⁾ = (tr W⁽ᵖ⁾ − Σ_{i≤k} θᵢ⁽ᵖ⁾)/(n − k)` (eq. (37)). -/
def ellBulk (Barr : ℕ → Fin k → ℝ) (F : Matrix (Fin k) (Fin n) ℝ) (Zarr : ℕ → Fin n → ℝ)
    (p : ℕ) : ℝ :=
  ((Wdual Barr F Zarr p).trace - ∑ i ∈ Finset.range k, theta Barr F Zarr p i) /
    ((n : ℝ) - k)

/-- Noiseless dual limit `W₀ = Fᵀ G_B F / n` (eq. (12)). -/
def W0 (GB : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / (n : ℝ)) • (Fᵀ * GB * F)

/-- `W = W₀ + (δ²/n) Iₙ` (eq. (12)). -/
def Wlim (GB : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) (δ2 : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  W0 GB F + (δ2 / n) • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- `λⱼ`, the `j`-th largest eigenvalue of `W₀` (Assumption 6). -/
def lam (GB : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) (j : ℕ) : ℝ :=
  sortedEigN (W0 GB F) j

/-- `Φ̄^∞ = diag(√μ) Vᵀ Σ_f^{-1/2} F` (eq. (50)), for an eigenbasis `V` of `K`. -/
def PhiBarInf (Sf GB V : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    Matrix (Fin k) (Fin n) ℝ :=
  Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf GB) j)) * Vᵀ *
    (CFC.sqrt Sf)⁻¹ * F

/-- `N = Φ̄^∞ (Φ̄^∞)ᵀ / n` (eq. (51)). -/
def Nlim (Sf GB V : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  (1 / (n : ℝ)) • (PhiBarInf Sf GB V F * (PhiBarInf Sf GB V F)ᵀ)

/-- Realized systematic coordinates `Φ = bᵀ B F` (Lemma 3, eq. (43)). -/
def PhiMat {p : ℕ} (b B : Matrix (Fin p) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    Matrix (Fin k) (Fin n) ℝ :=
  bᵀ * B * F

/-- `N⁽ᵖ⁾ = ΦΦᵀ/(np)` (eq. (13)). -/
def Npn {p : ℕ} (b B : Matrix (Fin p) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  (1 / ((n : ℝ) * p)) • (PhiMat b B F * (PhiMat b B F)ᵀ)

/-- `M̂ = G_B^{1/2} (F Fᵀ/n) G_B^{1/2}` (eq. (58)); it does not involve `Σ_f`. -/
def Mhat (GB : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt GB * ((1 / (n : ℝ)) • (F * Fᵀ)) * CFC.sqrt GB

/-- `Σ_O = G_B^{-1/2} Oᵀ Λ O G_B^{-1/2}` (eq. (61)). -/
def SigmaO (GB Λ O : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (CFC.sqrt GB)⁻¹ * Oᵀ * Λ * O * (CFC.sqrt GB)⁻¹

/-- Admissible factor covariances (eq. (60)): positive definite with `K(Σ)` isospectral
to `K(Σ_f)`. -/
def Admissible (Sf GB Sig : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  Sig.PosDef ∧ sortedEig (Kmat Sig GB) = sortedEig (Kmat Sf GB)

/-- `Λ = diag(μ₁, …, μ_k)`, the sorted eigenvalues of `K(Σ)` (eq. (59)). -/
def LamDiag (Sf GB : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal (sortedEig (Kmat Sf GB))

/-- The eigenbasis `V⁽ᵖ⁾ = Σ_f^{1/2} Bᵀ b Δ₀^{-1/2}` of `K⁽ᵖ⁾` attached to a principal
frame `b` (Proposition 1, eq. (46)), with `Δ₀ = p · diag(μ⁽ᵖ⁾)`. -/
def Vpn (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ)
    (b : Matrix (Fin p) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt Sf * (Bmat Barr p)ᵀ * b *
    Matrix.diagonal (fun j => 1 / Real.sqrt ((p : ℝ) * sortedEig (Kmat Sf (GBp Barr p)) j))

/-- `Δ₀^{1/2} = diag(√(p μⱼ⁽ᵖ⁾))` (Proposition 1). -/
def Delta0Sqrt (Barr : ℕ → Fin k → ℝ) (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal (fun j => Real.sqrt ((p : ℝ) * sortedEig (Kmat Sf (GBp Barr p)) j))

/-- `Q = Λ^{1/2} Vᵀ Σ_f^{-1/2}` (Remark after Proposition 2). -/
def Qmat (Sf GB V : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf GB) j)) * Vᵀ * (CFC.sqrt Sf)⁻¹

/-- The factor path `F⁽ⁿ⁾ = [f⁽¹⁾ ⋯ f⁽ⁿ⁾]` built from the first `n` draws of a sequence
(Corollary 3, where `n` varies). -/
def Fcols (f : ℕ → Fin k → ℝ) (n : ℕ) : Matrix (Fin k) (Fin n) ℝ :=
  Matrix.of fun a l => f l a

/-- The orthogonal projector `Π_H = H Hᵀ` onto the span of `h₁, …, h_k` (Corollary 1). -/
def projH {p : ℕ} (h : Fin k → EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  Hmat h * (Hmat h)ᵀ

/-- The Theorem 1 limit `δ²/(nλ+δ²) + nλ/(nλ+δ²) · s`. -/
def thm1Limit (n : ℕ) (δ2 lamj s : ℝ) : ℝ :=
  δ2 / ((n : ℝ) * lamj + δ2) + ((n : ℝ) * lamj / ((n : ℝ) * lamj + δ2)) * s

end PCError

end

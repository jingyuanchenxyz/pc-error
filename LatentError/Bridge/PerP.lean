import LatentError.Lemmas.Easy

/-!
# Bridge to Ono's `AsymptoticModel`: per-`p` data

Ono's bundle demands, for **every** admissible `p ≥ k`, a list of structural facts about
`(B, b, Φ, Z, h, w, ν, θ, νval, σ₀)`.  `PerP` packages exactly those facts for one `p`.
Real data satisfy them for all large `p`; `glue` supplies explicit data for the finitely many
remaining `p` (the limits in Ono's fields never see them).
-/

open scoped Matrix Topology MatrixOrder
open Filter

noncomputable section

namespace PCError

variable {k n : ℕ}

/-- Ono's per-`p` fields of `AsymptoticModel`, for a single `p`. -/
structure PerP (k n : ℕ) (hkn : k < n) (F : Matrix (Fin k) (Fin n) ℝ)
    (Sf : Matrix (Fin k) (Fin k) ℝ) (p : ℕ) where
  B : Matrix (Fin p) (Fin k) ℝ
  b : Matrix (Fin p) (Fin k) ℝ
  Φ : Matrix (Fin k) (Fin n) ℝ
  Z : Matrix (Fin p) (Fin n) ℝ
  h : Fin k → EuclideanSpace ℝ (Fin p)
  w : Fin k → EuclideanSpace ℝ (Fin n)
  ν : Fin k → EuclideanSpace ℝ (Fin k)
  θ : Fin n → ℝ
  νval : Fin k → ℝ
  sig0 : Fin k → ℝ
  hb_ortho : bᵀ * b = 1
  hB_rank : B.rank = k
  hcol_eq : LinearMap.range (Matrix.toEuclideanLin B) = LinearMap.range (Matrix.toEuclideanLin b)
  hBF : B * F = b * Φ
  hsig0_pos : ∀ j, 0 < sig0 j
  hsig0_sorted : StrictAnti sig0
  hb_eig : ∀ j : Fin k,
    Matrix.toEuclideanLin (B * Sf * Bᵀ) (colVec b j) = sig0 j • colVec b j
  hθ_sorted : Antitone θ
  hθ_spectrum : ∃ (hW : ((1 / ((n : ℝ) * p)) • ((b * Φ + Z)ᵀ * (b * Φ + Z))).IsHermitian)
      (e : Fin n ≃ Fin n), θ = fun i => hW.eigenvalues (e i)
  hh_unit : ∀ j, ‖h j‖ = 1
  hH_ortho : (Hmat h)ᵀ * (Hmat h) = 1
  hh_eig : ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / ((n : ℝ) * p)) • ((b * Φ + Z) * (b * Φ + Z)ᵀ)) (h j) =
      θ (Fin.castLE (le_of_lt hkn) j) • h j
  hw_unit : ∀ j, ‖w j‖ = 1
  hw_eig : ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / ((n : ℝ) * p)) • ((b * Φ + Z)ᵀ * (b * Φ + Z))) (w j) =
      θ (Fin.castLE (le_of_lt hkn) j) • w j
  hν_unit : ∀ j, ‖ν j‖ = 1
  hνval_sorted : Antitone νval
  hν_eig : ∀ j : Fin k,
    Matrix.toEuclideanLin ((1 / ((n : ℝ) * p)) • (Φ * Φᵀ)) (ν j) = νval j • ν j

/-! ## Generic spectral packages -/

/-- A chosen ordered eigenbasis (junk `1` for non-symmetric input). -/
def eigenbasisOf {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  if h : A.IsHermitian then Classical.choose (exists_isEigenbasis h) else 1

lemma isEigenbasis_eigenbasisOf {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) :
    IsEigenbasis A (eigenbasisOf A) := by
  rw [eigenbasisOf, dif_pos hA]; exact Classical.choose_spec (exists_isEigenbasis hA)

lemma sortedEig_eq_eigenvalues_comp {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) : ∃ e : Fin m ≃ Fin m, sortedEig A = fun i => hA.eigenvalues (e i) :=
  ⟨(finCongr (Fintype.card_fin m).symm).trans (Fintype.equivOfCardEq (Fintype.card_fin _)),
    by funext i; simp [sortedEig_of_isHermitian hA, Matrix.IsHermitian.eigenvalues]⟩

lemma gram_isHermitian {p m : ℕ} (Y : Matrix (Fin p) (Fin m) ℝ) (c : ℝ) :
    (c • (Yᵀ * Y)).IsHermitian :=
  isHermitian_of_transpose_eq (by simp [Matrix.transpose_mul])

lemma gram'_isHermitian {p m : ℕ} (Y : Matrix (Fin p) (Fin m) ℝ) (c : ℝ) :
    (c • (Y * Yᵀ)).IsHermitian :=
  isHermitian_of_transpose_eq (by simp [Matrix.transpose_mul])

/-- `S = cYYᵀ` and `W = cYᵀY` have the same padded sorted spectrum (`c ≥ 0`). -/
lemma sortedEigN_gram_swap {p m : ℕ} (Y : Matrix (Fin p) (Fin m) ℝ) {c : ℝ} (hc : 0 ≤ c) :
    sortedEigN (c • (Y * Yᵀ)) = sortedEigN (c • (Yᵀ * Y)) := by
  funext j
  rw [sortedEigN_smul (posSemidef_mul_transpose Y).isHermitian hc,
    sortedEigN_smul (posSemidef_transpose_mul Y).isHermitian hc, sortedEigN_mul_transpose]

/-- Columns `castLE j` of an orthogonal matrix form an orthonormal `k`-family. -/
lemma hmat_cols_orthonormal {m : ℕ} (hkm : k ≤ m) {U : Matrix (Fin m) (Fin m) ℝ}
    (hU : Uᵀ * U = 1) :
    (Hmat (fun j : Fin k => colVec U (Fin.castLE hkm j)))ᵀ *
      Hmat (fun j : Fin k => colVec U (Fin.castLE hkm j)) = 1 := by
  ext i j
  have h1 : ((Hmat (fun j : Fin k => colVec U (Fin.castLE hkm j)))ᵀ *
      Hmat (fun j : Fin k => colVec U (Fin.castLE hkm j))) i j =
      (Uᵀ * U) (Fin.castLE hkm i) (Fin.castLE hkm j) := by
    simp [Hmat, colVec, Matrix.mul_apply]
  rw [h1, hU, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.ext_iff]

lemma hmat_eq_of_colVec {p : ℕ} (h : Fin k → EuclideanSpace ℝ (Fin p)) :
    (Hmat h)ᵀ * Hmat h = Matrix.of fun i j => inner ℝ (h i) (h j) := by
  ext i j
  simp [Hmat, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- Eigenvectors of a symmetric matrix for distinct eigenvalues are orthogonal. -/
lemma inner_eq_zero_of_eigvec {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : Aᵀ = A)
    {u v : EuclideanSpace ℝ (Fin m)} {a c : ℝ} (hu : Matrix.toEuclideanLin A u = a • u)
    (hv : Matrix.toEuclideanLin A v = c • v) (hac : a ≠ c) : inner ℝ u v = 0 := by
  have h1 : inner ℝ (Matrix.toEuclideanLin A u) v = inner ℝ u (Matrix.toEuclideanLin A v) := by
    rw [inner_toEuclideanLin, hA]
  rw [hu, hv, real_inner_smul_left, real_inner_smul_right] at h1
  have : (a - c) * inner ℝ u v = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hac)

/-! ## Ranges -/

lemma range_toEuclideanLin_mul_le {p q r : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (N : Matrix (Fin q) (Fin r) ℝ) :
    LinearMap.range (Matrix.toEuclideanLin (M * N)) ≤ LinearMap.range (Matrix.toEuclideanLin M) := by
  rintro x ⟨y, rfl⟩
  exact ⟨Matrix.toEuclideanLin N y, (toEuclideanLin_mul M N y).symm⟩

lemma range_eq_of_factor {p : ℕ} {B b : Matrix (Fin p) (Fin k) ℝ}
    {M C : Matrix (Fin k) (Fin k) ℝ} (h1 : B = b * M) (h2 : b = B * C) :
    LinearMap.range (Matrix.toEuclideanLin B) = LinearMap.range (Matrix.toEuclideanLin b) := by
  apply le_antisymm
  · conv_lhs => rw [h1]
    exact range_toEuclideanLin_mul_le _ _
  · conv_lhs => rw [h2]
    exact range_toEuclideanLin_mul_le _ _

lemma rank_eq_of_transpose_mul_isUnit {p : ℕ} {B : Matrix (Fin p) (Fin k) ℝ}
    (h : IsUnit (Bᵀ * B).det) : B.rank = k := by
  rw [← Matrix.rank_transpose_mul_self, Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 h),
    Fintype.card_fin]

end PCError

end

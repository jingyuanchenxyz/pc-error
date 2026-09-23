import LatentError.Lemmas.Convergence

/-!
# The realized systematic duals (remark after Proposition 2, Corollary 2)

`Φ̄^∞ = Q F` with `Q = Λ^{1/2} Vᵀ Σ_f^{-1/2}`, `QᵀQ = G_B`, `Q Σ_f Qᵀ = Λ`; hence
`(Φ̄^∞)ᵀΦ̄^∞/n = W₀` and Gram duality relates `N` and `W₀`.
-/

open scoped Matrix Topology MatrixOrder
open Filter

noncomputable section

namespace PCError

variable {k n : ℕ}

section

variable {Sf GB V : Matrix (Fin k) (Fin k) ℝ}

lemma sqrt_inv_transpose (S : Matrix (Fin k) (Fin k) ℝ) :
    ((CFC.sqrt S)⁻¹)ᵀ = (CFC.sqrt S)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, sqrt_transpose]

lemma phiBarInf_eq_qmat (F : Matrix (Fin k) (Fin n) ℝ) :
    PhiBarInf Sf GB V F = Qmat Sf GB V * F := rfl

lemma diag_sqrt_mu_sq (hA5 : Assumption5 Sf GB) :
    Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf GB) j)) *
      Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf GB) j)) = LamDiag Sf GB :=
  diag_sqrt_mul_self fun j => (hA5.2 j).le

lemma qmat_sf_qmat (hSf : Sf.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) :
    Qmat Sf GB V * Sf * (Qmat Sf GB V)ᵀ = LamDiag Sf GB := by
  have hS : (CFC.sqrt Sf)⁻¹ * Sf * (CFC.sqrt Sf)⁻¹ = 1 := by
    have e : (CFC.sqrt Sf)⁻¹ * Sf * (CFC.sqrt Sf)⁻¹ =
        (CFC.sqrt Sf)⁻¹ * (CFC.sqrt Sf * CFC.sqrt Sf) * (CFC.sqrt Sf)⁻¹ := by
      rw [sqrt_mul_sqrt hSf]
    rw [e, ← Matrix.mul_assoc, sqrt_inv_mul hSf, Matrix.one_mul, sqrt_mul_inv hSf]
  calc Qmat Sf GB V * Sf * (Qmat Sf GB V)ᵀ
      = Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf GB) j)) *
          (Vᵀ * ((CFC.sqrt Sf)⁻¹ * Sf * (CFC.sqrt Sf)⁻¹) * V) *
          Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf GB) j)) := by
        simp only [Qmat, Matrix.transpose_mul, Matrix.transpose_transpose, sqrt_inv_transpose,
          Matrix.diagonal_transpose, Matrix.mul_assoc]
    _ = LamDiag Sf GB := by
        rw [hS, Matrix.mul_one, hV.1, Matrix.mul_one, diag_sqrt_mu_sq hA5]

lemma qmat_transpose_mul (hSf : Sf.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) : (Qmat Sf GB V)ᵀ * Qmat Sf GB V = GB := by
  have hK := hV.decomp
  calc (Qmat Sf GB V)ᵀ * Qmat Sf GB V
      = (CFC.sqrt Sf)⁻¹ * (V * (Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf GB) j)) *
          Matrix.diagonal (fun j => Real.sqrt (sortedEig (Kmat Sf GB) j))) * Vᵀ) *
          (CFC.sqrt Sf)⁻¹ := by
        simp only [Qmat, Matrix.transpose_mul, Matrix.transpose_transpose, sqrt_inv_transpose,
          Matrix.diagonal_transpose, Matrix.mul_assoc]
    _ = (CFC.sqrt Sf)⁻¹ * CFC.sqrt Sf * GB * (CFC.sqrt Sf * (CFC.sqrt Sf)⁻¹) := by
        rw [diag_sqrt_mu_sq hA5, LamDiag, ← hK, Kmat]
        simp only [Matrix.mul_assoc]
    _ = GB := by rw [sqrt_inv_mul hSf, sqrt_mul_inv hSf, Matrix.one_mul, Matrix.mul_one]

lemma qmat_sigmaHat (F : Matrix (Fin k) (Fin n) ℝ) :
    Qmat Sf GB V * ((1 / (n : ℝ)) • (F * Fᵀ)) * (Qmat Sf GB V)ᵀ = Nlim Sf GB V F := by
  simp only [Nlim, phiBarInf_eq_qmat, Matrix.transpose_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc]

lemma phiBarInf_gram (hSf : Sf.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) (F : Matrix (Fin k) (Fin n) ℝ) :
    (1 / (n : ℝ)) • ((PhiBarInf Sf GB V F)ᵀ * PhiBarInf Sf GB V F) = W0 GB F := by
  rw [phiBarInf_eq_qmat, W0, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ F,
    qmat_transpose_mul hSf hA5 hV, Matrix.mul_assoc]

/-- The factor `A = Φ̄^∞/√n` with `A Aᵀ = N` and `Aᵀ A = W₀`. -/
lemma nlim_eq (F : Matrix (Fin k) (Fin n) ℝ) :
    Nlim Sf GB V F = ((1 / Real.sqrt n) • PhiBarInf Sf GB V F) *
      ((1 / Real.sqrt n) • PhiBarInf Sf GB V F)ᵀ := by
  simp only [Nlim, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · have := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
    have : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
    field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma w0_eq (hSf : Sf.PosDef) (hA5 : Assumption5 Sf GB) (hV : IsEigenbasis (Kmat Sf GB) V)
    (F : Matrix (Fin k) (Fin n) ℝ) :
    W0 GB F = ((1 / Real.sqrt n) • PhiBarInf Sf GB V F)ᵀ *
      ((1 / Real.sqrt n) • PhiBarInf Sf GB V F) := by
  rw [← phiBarInf_gram hSf hA5 hV]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · have : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.2 hn)
    field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]

lemma sortedEigN_nlim (hSf : Sf.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) (F : Matrix (Fin k) (Fin n) ℝ) :
    sortedEigN (Nlim Sf GB V F) = sortedEigN (W0 GB F) := by
  rw [nlim_eq, w0_eq hSf hA5 hV, sortedEigN_mul_transpose]

lemma sortedEig_nlim (hSf : Sf.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) (F : Matrix (Fin k) (Fin n) ℝ) (j : Fin k) :
    sortedEig (Nlim Sf GB V F) j = lam GB F j := by
  have := congrFun (sortedEigN_nlim hSf hA5 hV F) j
  rwa [sortedEigN, dif_pos j.2] at this

lemma nlim_isHermitian (F : Matrix (Fin k) (Fin n) ℝ) : (Nlim Sf GB V F).IsHermitian := by
  rw [nlim_eq]; exact (posSemidef_mul_transpose _).isHermitian

/-- `Φ̄^∞ w/√(nλ)` is a unit eigenvector of `N`. -/
lemma nlim_eigvec_of_w0 (hSf : Sf.PosDef) (hA5 : Assumption5 Sf GB)
    (hV : IsEigenbasis (Kmat Sf GB) V) (F : Matrix (Fin k) (Fin n) ℝ)
    {w : EuclideanSpace ℝ (Fin n)} {l : ℝ} (hl : 0 < l) (hw : IsUnitEigvec (W0 GB F) w l) :
    IsUnitEigvec (Nlim Sf GB V F)
      ((1 / Real.sqrt ((n : ℝ) * l)) • Matrix.toEuclideanLin (PhiBarInf Sf GB V F) w) l := by
  have hw' : IsUnitEigvec (((1 / Real.sqrt n) • PhiBarInf Sf GB V F)ᵀ *
      ((1 / Real.sqrt n) • PhiBarInf Sf GB V F)ᵀᵀ) w l := by
    rwa [Matrix.transpose_transpose, ← w0_eq hSf hA5 hV]
  have h := gram_eigvec _ w l hl.ne' hw'
  try simp only [Matrix.transpose_transpose] at h
  rw [← nlim_eq] at h
  have hn : (n : ℝ) ≠ 0 := by
    rintro hn0
    have := hw.2
    simp only [W0, hn0, div_zero, zero_smul, map_zero, LinearMap.zero_apply] at this
    have h0 := congrArg norm this
    rw [norm_zero, norm_smul, hw.1, mul_one, Real.norm_eq_abs] at h0
    exact hl.ne' (abs_eq_zero.1 h0.symm)
  have hn' : 0 < (n : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hn)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn'
  have hsl : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
  convert h using 1
  rw [toEuclideanLin_smul_apply, smul_smul, Real.sqrt_mul hn'.le]
  congr 1
  field_simp

lemma n_pos_of_assumption6 {GB : Matrix (Fin k) (Fin k) ℝ} {F : Matrix (Fin k) (Fin n) ℝ}
    (hA6 : Assumption6 GB F) (j : Fin k) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · have := hA6.2 j
    simp [lam, sortedEigN] at this
  · exact h

end

end PCError

end

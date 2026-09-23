import LatentError.Bridge.PerP

/-!
# Completing per-`p` data, and explicit filler data for small `p`
-/

open scoped Matrix Topology MatrixOrder
open Filter

noncomputable section

namespace PCError

variable {k n : ℕ}

lemma sortedEigN_eq_fin {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (j : ℕ) (hj : j < m) :
    sortedEigN A j = sortedEig A ⟨j, hj⟩ := by
  rw [sortedEigN, dif_pos hj]

lemma isUnitEigvec_smul_sign {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}
    {v : EuclideanSpace ℝ (Fin m)} {μ s : ℝ} (hv : IsUnitEigvec A v μ) (hs : s = 1 ∨ s = -1) :
    IsUnitEigvec A (s • v) μ := by
  refine ⟨?_, ?_⟩
  · rw [norm_smul, hv.1, mul_one]; rcases hs with rfl | rfl <;> simp
  · rw [map_smul, hv.2, smul_comm]

/-- `S = cYYᵀ` and `W = cYᵀY` share the `j`-th sorted eigenvalue (`j < k ≤ p`, `k < n`). -/
lemma sortedEig_S_eq_W {p : ℕ} (hkp : k ≤ p) (hkn : k < n) (Y : Matrix (Fin p) (Fin n) ℝ)
    {c : ℝ} (hc : 0 ≤ c) (j : Fin k) :
    sortedEig (c • (Y * Yᵀ)) (Fin.castLE hkp j) = sortedEig (c • (Yᵀ * Y)) (Fin.castLE hkn.le j) := by
  have := congrFun (sortedEigN_gram_swap Y hc) j
  rwa [sortedEigN_eq_fin _ _ (lt_of_lt_of_le j.2 hkp),
    sortedEigN_eq_fin _ _ (lt_of_lt_of_le j.2 hkn.le)] at this

/-- Fill in the spectral fields (`θ`, `w`, `ν`, `νval`) of `PerP` from the structural ones,
given sample eigenvectors `h` and sign choices for `w` and `ν`. -/
def PerP.ofFrame {p : ℕ} (hkp : k ≤ p) (hkn : k < n) (F : Matrix (Fin k) (Fin n) ℝ)
    (Sf : Matrix (Fin k) (Fin k) ℝ)
    (B b : Matrix (Fin p) (Fin k) ℝ) (Φ : Matrix (Fin k) (Fin n) ℝ) (Z : Matrix (Fin p) (Fin n) ℝ)
    (sig0 : Fin k → ℝ) (h : Fin k → EuclideanSpace ℝ (Fin p)) (sw sν : Fin k → ℝ)
    (hb_ortho : bᵀ * b = 1) (hB_rank : B.rank = k)
    (hcol_eq : LinearMap.range (Matrix.toEuclideanLin B) =
      LinearMap.range (Matrix.toEuclideanLin b))
    (hBF : B * F = b * Φ) (hsig0_pos : ∀ j, 0 < sig0 j) (hsig0_sorted : StrictAnti sig0)
    (hb_eig : ∀ j : Fin k,
      Matrix.toEuclideanLin (B * Sf * Bᵀ) (colVec b j) = sig0 j • colVec b j)
    (hh_unit : ∀ j, ‖h j‖ = 1) (hH_ortho : (Hmat h)ᵀ * (Hmat h) = 1)
    (hh_eig : ∀ j : Fin k,
      Matrix.toEuclideanLin ((1 / ((n : ℝ) * p)) • ((b * Φ + Z) * (b * Φ + Z)ᵀ)) (h j) =
        sortedEig ((1 / ((n : ℝ) * p)) • ((b * Φ + Z)ᵀ * (b * Φ + Z))) (Fin.castLE hkn.le j) •
          h j)
    (hsw : ∀ j, sw j = 1 ∨ sw j = -1) (hsν : ∀ j, sν j = 1 ∨ sν j = -1) :
    PerP k n hkn F Sf p where
  B := B
  b := b
  Φ := Φ
  Z := Z
  h := h
  w := fun j => sw j • colVec (eigenbasisOf ((1 / ((n : ℝ) * p)) •
    ((b * Φ + Z)ᵀ * (b * Φ + Z)))) (Fin.castLE hkn.le j)
  ν := fun j => sν j • colVec (eigenbasisOf ((1 / ((n : ℝ) * p)) • (Φ * Φᵀ))) j
  θ := sortedEig ((1 / ((n : ℝ) * p)) • ((b * Φ + Z)ᵀ * (b * Φ + Z)))
  νval := sortedEig ((1 / ((n : ℝ) * p)) • (Φ * Φᵀ))
  sig0 := sig0
  hb_ortho := hb_ortho
  hB_rank := hB_rank
  hcol_eq := hcol_eq
  hBF := hBF
  hsig0_pos := hsig0_pos
  hsig0_sorted := hsig0_sorted
  hb_eig := hb_eig
  hθ_sorted := sortedEig_antitone _
  hθ_spectrum := ⟨gram_isHermitian _ _, sortedEig_eq_eigenvalues_comp _⟩
  hh_unit := hh_unit
  hH_ortho := hH_ortho
  hh_eig := hh_eig
  hw_unit := fun j => (isUnitEigvec_smul_sign
    ((isEigenbasis_eigenbasisOf (gram_isHermitian _ _)).isUnitEigvec _) (hsw j)).1
  hw_eig := fun j => (isUnitEigvec_smul_sign
    ((isEigenbasis_eigenbasisOf (gram_isHermitian _ _)).isUnitEigvec _) (hsw j)).2
  hν_unit := fun j => (isUnitEigvec_smul_sign
    ((isEigenbasis_eigenbasisOf (gram'_isHermitian _ _)).isUnitEigvec j) (hsν j)).1
  hνval_sorted := sortedEig_antitone _
  hν_eig := fun j => (isUnitEigvec_smul_sign
    ((isEigenbasis_eigenbasisOf (gram'_isHermitian _ _)).isUnitEigvec j) (hsν j)).2

/-! ## Filler data -/

lemma padId_tm {p : ℕ} (hkp : k ≤ p) : (padId p k)ᵀ * padId p k = 1 :=
  padId_transpose_mul hkp

/-- `cⱼ = k − j`, positive and strictly decreasing. -/
def cvec (k : ℕ) : Fin k → ℝ := fun j => (k : ℝ) - j

lemma cvec_pos (j : Fin k) : 0 < cvec k j := by
  have := j.2; unfold cvec
  have : (j : ℝ) < k := by exact_mod_cast this
  linarith

lemma cvec_sq_strictAnti : StrictAnti (fun j : Fin k => cvec k j * cvec k j) := by
  intro i j hij
  have hij' : (i : ℝ) < j := by exact_mod_cast hij
  have hj := cvec_pos j
  have hlt : cvec k j < cvec k i := by unfold cvec; linarith
  exact mul_self_lt_mul_self hj.le hlt

lemma sqrt_inv_mul_mul_sqrt_inv {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosDef) :
    (CFC.sqrt S)⁻¹ * S * (CFC.sqrt S)⁻¹ = 1 := by
  have e : (CFC.sqrt S)⁻¹ * S * (CFC.sqrt S)⁻¹ =
      (CFC.sqrt S)⁻¹ * (CFC.sqrt S * CFC.sqrt S) * (CFC.sqrt S)⁻¹ := by
    rw [sqrt_mul_sqrt hS]
  rw [e, ← Matrix.mul_assoc, sqrt_inv_mul hS, Matrix.one_mul, sqrt_mul_inv hS]

section glue

variable {Sf : Matrix (Fin k) (Fin k) ℝ}

/-- `C_g = diag(c) Σ_f^{-1/2}` and its inverse. -/
def Cg (Sf : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal (cvec k) * (CFC.sqrt Sf)⁻¹

def CgInv (Sf : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  CFC.sqrt Sf * Matrix.diagonal (fun j => 1 / cvec k j)

lemma diag_c_mul_inv : Matrix.diagonal (cvec k) * Matrix.diagonal (fun j => 1 / cvec k j) = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j; have := (cvec_pos j).ne'; field_simp

lemma cg_mul_inv (hSf : Sf.PosDef) : Cg Sf * CgInv Sf = 1 := by
  rw [Cg, CgInv, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt Sf)⁻¹, sqrt_inv_mul hSf,
    Matrix.one_mul, diag_c_mul_inv]

lemma cg_sf_cg (hSf : Sf.PosDef) :
    Cg Sf * Sf * (Cg Sf)ᵀ = Matrix.diagonal (fun j => cvec k j * cvec k j) := by
  rw [Cg, Matrix.transpose_mul, sqrt_inv_transpose, Matrix.diagonal_transpose]
  calc Matrix.diagonal (cvec k) * (CFC.sqrt Sf)⁻¹ * Sf *
        ((CFC.sqrt Sf)⁻¹ * Matrix.diagonal (cvec k))
      = Matrix.diagonal (cvec k) * ((CFC.sqrt Sf)⁻¹ * Sf * (CFC.sqrt Sf)⁻¹) *
          Matrix.diagonal (cvec k) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [sqrt_inv_mul_mul_sqrt_inv hSf, Matrix.mul_one, Matrix.diagonal_mul_diagonal]

/-- The filler data matrix `Y = E (C_g F)`. -/
def glueY (Sf : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) (p : ℕ) :
    Matrix (Fin p) (Fin n) ℝ :=
  padId p k * (Cg Sf * F) + 0

/-- Explicit data satisfying every per-`p` field (used for `k ≤ p < p₀`). -/
def glue (hSf : Sf.PosDef) (hkn : k < n) (F : Matrix (Fin k) (Fin n) ℝ) {p : ℕ}
    (hkp : k ≤ p) : PerP k n hkn F Sf p := by
  let U := eigenbasisOf ((1 / ((n : ℝ) * p)) • (glueY Sf F p * (glueY Sf F p)ᵀ))
  have hU : IsEigenbasis ((1 / ((n : ℝ) * p)) • (glueY Sf F p * (glueY Sf F p)ᵀ)) U :=
    isEigenbasis_eigenbasisOf (gram'_isHermitian _ _)
  refine PerP.ofFrame hkp hkn F Sf (padId p k * Cg Sf) (padId p k) (Cg Sf * F) 0
    (fun j => cvec k j * cvec k j) (fun j => colVec U (Fin.castLE hkp j))
    (fun _ => 1) (fun _ => 1) (padId_tm hkp) ?_ ?_ (Matrix.mul_assoc _ _ _)
    (fun j => mul_pos (cvec_pos j) (cvec_pos j)) cvec_sq_strictAnti ?_
    (fun j => norm_colVec U hU.1 _) (hmat_cols_orthonormal hkp hU.1) ?_
    (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)
  · refine rank_eq_of_transpose_mul_isUnit (Matrix.isUnit_det_of_left_inverse
      (B := CgInv Sf * (CgInv Sf)ᵀ) ?_)
    calc CgInv Sf * (CgInv Sf)ᵀ * ((padId p k * Cg Sf)ᵀ * (padId p k * Cg Sf))
        = CgInv Sf * ((Cg Sf * CgInv Sf)ᵀ * ((padId p k)ᵀ * padId p k) * Cg Sf) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [cg_mul_inv hSf, Matrix.transpose_one, Matrix.one_mul, padId_tm hkp,
            Matrix.one_mul]
          exact mul_eq_one_comm.1 (cg_mul_inv hSf)
  · exact range_eq_of_factor rfl (by rw [Matrix.mul_assoc, cg_mul_inv hSf, Matrix.mul_one])
  · intro j
    have hm : padId p k * Cg Sf * Sf * (padId p k * Cg Sf)ᵀ * padId p k =
        padId p k * Matrix.diagonal (fun j => cvec k j * cvec k j) := by
      calc padId p k * Cg Sf * Sf * (padId p k * Cg Sf)ᵀ * padId p k
          = padId p k * (Cg Sf * Sf * (Cg Sf)ᵀ) * ((padId p k)ᵀ * padId p k) := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = _ := by rw [cg_sf_cg hSf, padId_tm hkp, Matrix.mul_one]
    rw [← colVec_mul, hm, colVec_mul_diagonal]
  · intro j
    have e := sortedEig_S_eq_W hkp hkn (glueY Sf F p) (c := 1 / ((n : ℝ) * p)) (by positivity) j
    have hj := (hU.isUnitEigvec (Fin.castLE hkp j)).2
    rw [e] at hj
    exact hj

end glue

end PCError

end

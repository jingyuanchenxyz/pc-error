import LatentError.Lemmas.Spectral

/-!
# Ordered orthonormal eigenbases

Existence of `IsEigenbasis`, and computing `sortedEig` from an orthogonal
diagonalization (used for scalings/shifts and for `W = W₀ + (δ²/n) I`).
-/

open scoped Matrix Topology MatrixOrder
open Filter Polynomial

noncomputable section

namespace PCError

/-! ## Columns -/

lemma colVec_mul {p q r : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) (U : Matrix (Fin q) (Fin r) ℝ)
    (j : Fin r) : colVec (A * U) j = Matrix.toEuclideanLin A (colVec U j) := by
  ext i
  simp [colVec, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]

lemma transpose_mul_apply_eq_inner {p r : ℕ} (U : Matrix (Fin p) (Fin r) ℝ) (i j : Fin r) :
    (Uᵀ * U) i j = inner ℝ (colVec U i) (colVec U j) := by
  simp [colVec, Matrix.mul_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

lemma colVec_mul_diagonal {p r : ℕ} (U : Matrix (Fin p) (Fin r) ℝ) (d : Fin r → ℝ) (j : Fin r) :
    colVec (U * Matrix.diagonal d) j = d j • colVec U j := by
  ext i
  simp [colVec, Matrix.mul_diagonal, mul_comm]

lemma mul_diagonal_add_smul {p r : ℕ} (U : Matrix (Fin p) (Fin r) ℝ) (d : Fin r → ℝ) (c : ℝ) :
    U * Matrix.diagonal d + c • U = U * Matrix.diagonal (fun i => d i + c) := by
  ext i j
  simp [Matrix.mul_diagonal, mul_add, mul_comm]

lemma ext_colVec {p r : ℕ} {M N : Matrix (Fin p) (Fin r) ℝ} (h : ∀ j, colVec M j = colVec N j) :
    M = N := by
  ext i j
  simpa [colVec] using congrArg (fun v : EuclideanSpace ℝ (Fin p) => v i) (h j)

/-! ## `IsEigenbasis` -/

lemma IsEigenbasis.mul_transpose {k : ℕ} {K U : Matrix (Fin k) (Fin k) ℝ}
    (hU : IsEigenbasis K U) : U * Uᵀ = 1 :=
  mul_eq_one_comm.1 hU.1

lemma IsEigenbasis.decomp {k : ℕ} {K U : Matrix (Fin k) (Fin k) ℝ} (hU : IsEigenbasis K U) :
    K = U * Matrix.diagonal (sortedEig K) * Uᵀ := by
  rw [← hU.2, Matrix.mul_assoc, hU.mul_transpose, Matrix.mul_one]

lemma IsEigenbasis.isUnitEigvec {k : ℕ} {K U : Matrix (Fin k) (Fin k) ℝ}
    (hU : IsEigenbasis K U) (j : Fin k) : IsUnitEigvec K (colVec U j) (sortedEig K j) :=
  ⟨norm_colVec U hU.1 j, by rw [← colVec_mul, hU.2, colVec_mul_diagonal]⟩

lemma exists_isEigenbasis {k : ℕ} {K : Matrix (Fin k) (Fin k) ℝ} (hK : K.IsHermitian) :
    ∃ U, IsEigenbasis K U := by
  set hT := isSymmetric_of_isHermitian hK
  set u : Fin k → EuclideanSpace ℝ (Fin k) := fun j =>
    hT.eigenvectorBasis finrank_euclideanSpace (Fin.cast (Fintype.card_fin k).symm j)
  set U : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => u j i
  have hcol : ∀ j, colVec U j = u j := fun j => by ext i; simp [colVec, U]
  refine ⟨U, ?_, ext_colVec fun j => ?_⟩
  · ext i j
    rw [transpose_mul_apply_eq_inner, hcol, hcol, Matrix.one_apply]
    have := orthonormal_iff_ite.1 (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal
      (Fin.cast (Fintype.card_fin k).symm i) (Fin.cast (Fintype.card_fin k).symm j)
    simpa [u, Fin.ext_iff] using this
  · rw [colVec_mul, colVec_mul_diagonal, hcol, sortedEig_of_isHermitian hK, eigenvalues₀_eq]
    exact (hT.hasEigenvector_eigenvectorBasis finrank_euclideanSpace _).apply_eq_smul

/-- The sorted spectrum of `U · diag d · Uᵀ` (orthogonal `U`, antitone `d`) is `d`. -/
lemma sortedEig_eq_of_decomp {m : ℕ} {A U : Matrix (Fin m) (Fin m) ℝ} {d : Fin m → ℝ}
    (hU : Uᵀ * U = 1) (hd : Antitone d) (hA : A = U * Matrix.diagonal d * Uᵀ) :
    sortedEig A = d := by
  have hAH : A.IsHermitian := by
    rw [hA, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hchar : A.charpoly = (Matrix.diagonal d).charpoly := by
    rw [hA, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hU, Matrix.mul_one]
  have hroots : A.charpoly.roots = Finset.univ.val.map d := by
    rw [hchar, Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  apply List.ofFn_injective
  rw [ofFn_sortedEig hAH, rootList, hroots]
  apply List.Perm.eq_of_sortedGE
  · exact List.sortedGE_iff_pairwise.2 (Multiset.pairwise_sort _ _)
  · exact hd.sortedGE_ofFn
  · rw [← Multiset.coe_eq_coe, Multiset.sort_eq, Fin.univ_val_map]

lemma sortedEig_eq_of_mul_eq {m : ℕ} {A U : Matrix (Fin m) (Fin m) ℝ} {d : Fin m → ℝ}
    (hU : Uᵀ * U = 1) (hd : Antitone d) (hAU : A * U = U * Matrix.diagonal d) :
    sortedEig A = d := by
  refine sortedEig_eq_of_decomp hU hd ?_
  rw [← hAU, Matrix.mul_assoc, mul_eq_one_comm.1 hU, Matrix.mul_one]

lemma sortedEig_smul {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) {c : ℝ}
    (hc : 0 ≤ c) : sortedEig (c • A) = fun i => c * sortedEig A i := by
  obtain ⟨U, hU⟩ := exists_isEigenbasis hA
  refine sortedEig_eq_of_mul_eq hU.1 (fun i j hij => ?_) ?_
  · exact mul_le_mul_of_nonneg_left (sortedEig_antitone A hij) hc
  · rw [Matrix.smul_mul, hU.2, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    rfl

lemma sortedEig_add_smul_one {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian)
    (c : ℝ) : sortedEig (A + c • 1) = fun i => sortedEig A i + c := by
  obtain ⟨U, hU⟩ := exists_isEigenbasis hA
  refine sortedEig_eq_of_mul_eq hU.1 (fun i j hij => ?_) ?_
  · linarith [sortedEig_antitone A hij]
  · rw [Matrix.add_mul, hU.2, Matrix.smul_mul, Matrix.one_mul, mul_diagonal_add_smul]

lemma sortedEigN_smul {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) {c : ℝ}
    (hc : 0 ≤ c) (j : ℕ) : sortedEigN (c • A) j = c * sortedEigN A j := by
  unfold sortedEigN
  split_ifs with hj
  · rw [sortedEig_smul hA hc]
  · simp

end PCError

end

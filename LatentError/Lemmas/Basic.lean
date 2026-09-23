import LatentError.Defs

/-!
# Basic helper lemmas: matrices acting on Euclidean space, projectors, `sinSq`

Proof infrastructure only (no new statements of paper results).
-/

open scoped Matrix Topology MatrixOrder
open Filter

noncomputable section

namespace PCError

variable {k n : ℕ}

/-! ## `toEuclideanLin` -/

lemma toEuclideanLin_mul {p q r : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Matrix (Fin q) (Fin r) ℝ) (v : EuclideanSpace ℝ (Fin r)) :
    Matrix.toEuclideanLin (M * A) v =
      Matrix.toEuclideanLin M (Matrix.toEuclideanLin A v) := by
  simp only [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

@[simp] lemma toEuclideanLin_one_apply {p : ℕ} (v : EuclideanSpace ℝ (Fin p)) :
    Matrix.toEuclideanLin (1 : Matrix (Fin p) (Fin p) ℝ) v = v := by
  simp

lemma toEuclideanLin_sub_apply {p q : ℕ} (M N : Matrix (Fin p) (Fin q) ℝ)
    (v : EuclideanSpace ℝ (Fin q)) :
    Matrix.toEuclideanLin (M - N) v = Matrix.toEuclideanLin M v - Matrix.toEuclideanLin N v := by
  rw [map_sub, LinearMap.sub_apply]

lemma toEuclideanLin_smul_apply {p q : ℕ} (c : ℝ) (M : Matrix (Fin p) (Fin q) ℝ)
    (v : EuclideanSpace ℝ (Fin q)) :
    Matrix.toEuclideanLin (c • M) v = c • Matrix.toEuclideanLin M v := by
  rw [map_smul, LinearMap.smul_apply]

/-- The transpose is the adjoint. -/
lemma inner_toEuclideanLin {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (x : EuclideanSpace ℝ (Fin q)) (y : EuclideanSpace ℝ (Fin p)) :
    inner ℝ (Matrix.toEuclideanLin M x) y = inner ℝ x (Matrix.toEuclideanLin Mᵀ y) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, star_trivial]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

/-- `‖M v‖² = ⟪v, MᵀM v⟫`. -/
lemma norm_toEuclideanLin_sq {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ)
    (v : EuclideanSpace ℝ (Fin q)) :
    ‖Matrix.toEuclideanLin M v‖ ^ 2 = inner ℝ v (Matrix.toEuclideanLin (Mᵀ * M) v) := by
  rw [← real_inner_self_eq_norm_sq, inner_toEuclideanLin, toEuclideanLin_mul]

/-- Orthonormal columns preserve inner products. -/
lemma inner_toEuclideanLin_of_orthonormal {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ)
    (hb : bᵀ * b = 1) (x y : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (Matrix.toEuclideanLin b x) (Matrix.toEuclideanLin b y) = inner ℝ x y := by
  rw [inner_toEuclideanLin, ← toEuclideanLin_mul, hb, toEuclideanLin_one_apply]

lemma norm_toEuclideanLin_of_orthonormal {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ)
    (hb : bᵀ * b = 1) (x : EuclideanSpace ℝ (Fin k)) :
    ‖Matrix.toEuclideanLin b x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner,
    inner_toEuclideanLin_of_orthonormal b hb]

/-! ## Columns and the projector `Π = b bᵀ` -/

lemma colVec_eq_toEuclideanLin {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (j : Fin k) :
    colVec b j = Matrix.toEuclideanLin b (e j) := by
  ext i
  simp [colVec, Matrix.toLpLin_apply]

lemma norm_colVec {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1) (j : Fin k) :
    ‖colVec b j‖ = 1 := by
  rw [colVec_eq_toEuclideanLin, norm_toEuclideanLin_of_orthonormal b hb]
  simp

lemma projB_transpose {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) : (projB b)ᵀ = projB b := by
  simp [projB, Matrix.transpose_mul]

lemma projB_mul_self {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1) :
    projB b * projB b = projB b := by
  simp only [projB]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc bᵀ, hb, Matrix.one_mul]

lemma projB_mul_self_left {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1) :
    projB b * b = b := by
  simp only [projB]
  rw [Matrix.mul_assoc, hb, Matrix.mul_one]

lemma projB_colVec {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1) (j : Fin k) :
    Matrix.toEuclideanLin (projB b) (colVec b j) = colVec b j := by
  rw [colVec_eq_toEuclideanLin, ← toEuclideanLin_mul, projB_mul_self_left b hb]

/-- `⟪Π u, v⟫ = ⟪u, Π v⟫`. -/
lemma inner_projB_left {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (u v : EuclideanSpace ℝ (Fin p)) :
    inner ℝ (Matrix.toEuclideanLin (projB b) u) v =
      inner ℝ u (Matrix.toEuclideanLin (projB b) v) := by
  rw [inner_toEuclideanLin, projB_transpose]

/-- `‖Π u‖² = ⟪u, Π u⟫`. -/
lemma norm_projB_sq {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (u : EuclideanSpace ℝ (Fin p)) :
    ‖Matrix.toEuclideanLin (projB b) u‖ ^ 2 =
      inner ℝ u (Matrix.toEuclideanLin (projB b) u) := by
  rw [← real_inner_self_eq_norm_sq, inner_projB_left, ← toEuclideanLin_mul,
    projB_mul_self b hb]

/-- `⟪u, bⱼ⟫ = ⟪Π u, bⱼ⟫`. -/
lemma inner_colVec_eq_inner_projB {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (u : EuclideanSpace ℝ (Fin p)) (j : Fin k) :
    inner ℝ u (colVec b j) = inner ℝ (Matrix.toEuclideanLin (projB b) u) (colVec b j) := by
  rw [inner_projB_left, projB_colVec b hb]

/-- `‖(1 − Π) u‖² = ‖u‖² − ‖Π u‖²`. -/
lemma norm_one_sub_projB_sq {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (u : EuclideanSpace ℝ (Fin p)) :
    ‖Matrix.toEuclideanLin (1 - projB b) u‖ ^ 2 =
      ‖u‖ ^ 2 - ‖Matrix.toEuclideanLin (projB b) u‖ ^ 2 := by
  rw [toEuclideanLin_sub_apply, toEuclideanLin_one_apply, @norm_sub_sq_real,
    ← norm_projB_sq b hb]
  ring

/-! ## `sinSq` -/

lemma sinSq_of_unit {m : ℕ} {u v : EuclideanSpace ℝ (Fin m)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    sinSq u v = 1 - inner ℝ u v ^ 2 := by
  simp [sinSq, hu, hv]

lemma sinSq_mem_Icc_of_unit {m : ℕ} {u v : EuclideanSpace ℝ (Fin m)}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : sinSq u v ∈ Set.Icc (0 : ℝ) 1 := by
  rw [sinSq_of_unit hu hv]
  have h := abs_real_inner_le_norm u v
  rw [hu, hv, one_mul] at h
  have h2 : inner ℝ u v ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (inner ℝ u v)]
  constructor <;> nlinarith [sq_nonneg (inner ℝ u v)]

lemma sinSq_tendsto {m : ℕ} {ι : Type*} {L : Filter ι}
    {up vp : ι → EuclideanSpace ℝ (Fin m)} {u v : EuclideanSpace ℝ (Fin m)}
    (hu : u ≠ 0) (hv : v ≠ 0) (hup : Tendsto up L (𝓝 u)) (hvp : Tendsto vp L (𝓝 v)) :
    Tendsto (fun i => sinSq (up i) (vp i)) L (𝓝 (sinSq u v)) := by
  unfold sinSq
  have hden : ‖u‖ ^ 2 * ‖v‖ ^ 2 ≠ 0 := by
    have := norm_ne_zero_iff.mpr hu; have := norm_ne_zero_iff.mpr hv; positivity
  exact tendsto_const_nhds.sub
    (((hup.inner hvp).pow 2).div ((hup.norm.pow 2).mul (hvp.norm.pow 2)) hden)

lemma sinSq_smul_left {m : ℕ} {a : ℝ} (ha : a ≠ 0) (u v : EuclideanSpace ℝ (Fin m)) :
    sinSq (a • u) v = sinSq u v := by
  unfold sinSq
  rw [real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
  congr 1
  by_cases hden : ‖u‖ ^ 2 * ‖v‖ ^ 2 = 0
  · rw [mul_assoc, hden]; simp
  · rw [mul_assoc, mul_div_mul_left _ _ (pow_ne_zero 2 ha)]

lemma sinSq_neg_left {m : ℕ} (u v : EuclideanSpace ℝ (Fin m)) : sinSq (-u) v = sinSq u v := by
  simp [sinSq]

/-! ## `frobSq` -/

lemma frobSq_eq_trace {m l : ℕ} (M : Matrix (Fin m) (Fin l) ℝ) :
    frobSq M = (Mᵀ * M).trace := by
  simp only [frobSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, sq]
  exact Finset.sum_comm

end PCError

end

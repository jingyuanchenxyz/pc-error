import LatentError.Lemmas.AlgLeaves
import LatentError.Lemmas.Duality

/-!
# Leaf lemmas, batch 3

Small goals for the local harness (`harness/prove.py --all`); hints are in comments.
* Corollary 3: conjugated limits, the spectrum and eigenvectors of `Λ = diag μ`, and
  `sin² → 0` from `|⟪·,·⟫| → 1`.
* Lemma 6: `G_B^{1/2} Σ_O G_B^{1/2} = Oᵀ Λ O`, and `M̂`, `W₀` as Gram matrices of
  `G_B^{1/2} F/√n` (so they share their spectrum and `W₀` has rank `≤ k`).
* Theorem 2: `tr W₀ = Σⱼ λⱼ`, the bulk-average algebra, and the ratio limit.
* Corollary 1: traces of projectors and Frobenius-norm identities.
-/

open MeasureTheory Filter
open scoped Topology Matrix MatrixOrder

noncomputable section

namespace PCError

variable {k n : ℕ}

/-! ## Corollary 3 -/

lemma tendsto_conj {ι : Type*} {L : Filter ι} {a b : ℕ} (Q : Matrix (Fin a) (Fin b) ℝ)
    {S : ι → Matrix (Fin b) (Fin b) ℝ} {S0 : Matrix (Fin b) (Fin b) ℝ}
    (h : Tendsto S L (𝓝 S0)) : Tendsto (fun t => Q * S t * Qᵀ) L (𝓝 (Q * S0 * Qᵀ)) := by
  -- hint: exact tendsto_matrix_mul (tendsto_matrix_mul tendsto_const_nhds h) tendsto_const_nhds
  exact tendsto_matrix_mul (tendsto_matrix_mul tendsto_const_nhds h) tendsto_const_nhds

lemma sortedEig_diagonal_antitone {m : ℕ} {d : Fin m → ℝ} (hd : Antitone d) :
    sortedEig (Matrix.diagonal d) = d := by
  -- hint: exact sortedEig_eq_of_mul_eq (U := 1) (by simp) hd (by simp)
  exact sortedEig_eq_of_mul_eq (U := 1) (by simp) hd (by simp)

lemma sortedEig_lamDiag (Sf GB : Matrix (Fin k) (Fin k) ℝ) :
    sortedEig (LamDiag Sf GB) = sortedEig (Kmat Sf GB) := by
  -- hint: exact sortedEig_diagonal_antitone (sortedEig_antitone _)
  unfold LamDiag
  exact sortedEig_diagonal_antitone (sortedEig_antitone _)

lemma lamDiag_isHermitian (Sf GB : Matrix (Fin k) (Fin k) ℝ) : (LamDiag Sf GB).IsHermitian := by
  -- hint: exact isHermitian_of_transpose_eq (by simp [LamDiag])
  exact isHermitian_of_transpose_eq (by simp [LamDiag])

lemma isUnitEigvec_diagonal_e (d : Fin k → ℝ) (j : Fin k) :
    IsUnitEigvec (Matrix.diagonal d) (e j) (d j) := by
  -- hint: refine ⟨by simp [e], ?_⟩; ext i
  -- simp [e, Matrix.toLpLin_apply, Matrix.mulVec_diagonal, Pi.single_apply]; split_ifs <;> simp_all
  refine ⟨by simp [e], ?_⟩
  ext i
  simp [e, Matrix.toLpLin_apply, Matrix.mulVec_diagonal, EuclideanSpace.single_apply]

lemma sinSq_tendsto_zero_of_abs_inner {m : ℕ} {u : ℕ → EuclideanSpace ℝ (Fin m)}
    {v : EuclideanSpace ℝ (Fin m)} (hu : ∀ᶠ p in atTop, ‖u p‖ = 1) (hv : ‖v‖ = 1)
    (h : Tendsto (fun p => |inner ℝ (u p) v|) atTop (𝓝 1)) :
    Tendsto (fun p => sinSq (u p) v) atTop (𝓝 0) := by
  -- hint: have h2 := (h.pow 2).const_sub 1; rw [one_pow, sub_self] at h2
  -- refine h2.congr' ?_; filter_upwards [hu] with p hp; rw [sinSq_of_unit hp hv, sq_abs]
  have h2 := (h.pow 2).const_sub 1
  rw [one_pow, sub_self] at h2
  refine h2.congr' ?_
  filter_upwards [hu] with p hp
  rw [sinSq_of_unit hp hv, sq_abs]

/-! ## Lemma 6 -/

lemma sqrt_gb_sigmaO {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GB.PosDef)
    (Λ O : Matrix (Fin k) (Fin k) ℝ) :
    CFC.sqrt GB * SigmaO GB Λ O * CFC.sqrt GB = Oᵀ * Λ * O := by
  -- hint: simp only [SigmaO, Matrix.mul_assoc]; rw [sqrt_inv_mul hGB, Matrix.mul_one]
  -- rw [← Matrix.mul_assoc (CFC.sqrt GB) (CFC.sqrt GB)⁻¹, sqrt_mul_inv hGB, Matrix.one_mul]
  simp only [SigmaO, Matrix.mul_assoc]
  rw [sqrt_inv_mul hGB, Matrix.mul_one]
  rw [← Matrix.mul_assoc (CFC.sqrt GB) (CFC.sqrt GB)⁻¹, sqrt_mul_inv hGB, Matrix.one_mul]

lemma one_div_sqrt_mul_self (n : ℕ) :
    (1 / Real.sqrt n) * (1 / Real.sqrt n) = 1 / (n : ℝ) := by
  -- hint: rw [one_div_mul_one_div, Real.mul_self_sqrt (Nat.cast_nonneg n)]
  rw [one_div_mul_one_div, Real.mul_self_sqrt (Nat.cast_nonneg n)]

lemma mhat_eq_gram (GB : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    Mhat GB F = ((1 / Real.sqrt n) • (CFC.sqrt GB * F)) *
      ((1 / Real.sqrt n) • (CFC.sqrt GB * F))ᵀ := by
  -- hint: simp only [Mhat, Matrix.transpose_smul, Matrix.transpose_mul, sqrt_transpose,
  --   Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, one_div_sqrt_mul_self]
  simp only [Mhat, Matrix.transpose_smul, Matrix.transpose_mul, sqrt_transpose,
  Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, one_div_sqrt_mul_self]

lemma w0_eq_gram {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GB.PosDef)
    (F : Matrix (Fin k) (Fin n) ℝ) :
    W0 GB F = ((1 / Real.sqrt n) • (CFC.sqrt GB * F))ᵀ *
      ((1 / Real.sqrt n) • (CFC.sqrt GB * F)) := by
  -- hint: simp only [W0, Matrix.transpose_smul, Matrix.transpose_mul, sqrt_transpose,
  --   Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, one_div_sqrt_mul_self]
  -- rw [← Matrix.mul_assoc (CFC.sqrt GB) (CFC.sqrt GB) F, sqrt_mul_sqrt hGB]
  simp only [W0, Matrix.transpose_smul, Matrix.transpose_mul, sqrt_transpose,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, one_div_sqrt_mul_self]
  rw [← Matrix.mul_assoc (CFC.sqrt GB) (CFC.sqrt GB) F, sqrt_mul_sqrt hGB]

lemma mhat_transpose (GB : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ) :
    (Mhat GB F)ᵀ = Mhat GB F := by
  -- hint: simp [Mhat, Matrix.transpose_mul, sqrt_transpose, Matrix.mul_assoc]
  simp [Mhat, Matrix.transpose_mul, sqrt_transpose, Matrix.mul_assoc]

lemma sortedEigN_mhat {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GB.PosDef)
    (F : Matrix (Fin k) (Fin n) ℝ) : sortedEigN (Mhat GB F) = sortedEigN (W0 GB F) := by
  -- hint: rw [mhat_eq_gram, w0_eq_gram hGB]; exact sortedEigN_mul_transpose _
  rw [mhat_eq_gram, w0_eq_gram hGB]
  exact sortedEigN_mul_transpose _

lemma sortedEigN_w0_eq_zero {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GB.PosDef)
    (F : Matrix (Fin k) (Fin n) ℝ) (i : ℕ) (hi : k ≤ i) : sortedEigN (W0 GB F) i = 0 := by
  -- hint: rw [← sortedEigN_mhat hGB F]; simp [sortedEigN, not_lt.2 hi]
  rw [← sortedEigN_mhat hGB F]; simp [sortedEigN, not_lt.2 hi]

/-! ## Theorem 2 -/

lemma sum_range_eq_sum_fin (f : ℕ → ℝ) : ∑ i ∈ Finset.range k, f i = ∑ j : Fin k, f j := by
  -- hint: exact (Fin.sum_univ_eq_sum_range f k).symm
  exact (Fin.sum_univ_eq_sum_range f k).symm

lemma trace_w0_eq_sum_lam {GB : Matrix (Fin k) (Fin k) ℝ} (hGB : GB.PosDef) (hkn : k ≤ n)
    (F : Matrix (Fin k) (Fin n) ℝ) : (W0 GB F).trace = ∑ j : Fin k, lam GB F j := by
  -- hint: have hs : GBᵀ = GB := transpose_eq_of_isHermitian hGB.isHermitian
  -- rw [trace_eq_sum_sortedEig (w0_isHermitian hs F)]
  -- have h1 : ∑ j : Fin n, sortedEig (W0 GB F) j =
  --     ∑ i ∈ Finset.range n, sortedEigN (W0 GB F) i := by
  --   rw [← Fin.sum_univ_eq_sum_range]; simp [sortedEigN]
  -- have h2 : ∑ j : Fin k, lam GB F j = ∑ i ∈ Finset.range k, sortedEigN (W0 GB F) i := by
  --   rw [← Fin.sum_univ_eq_sum_range]; rfl
  -- rw [h1, h2, ← Finset.sum_range_add_sum_Ico _ hkn, Finset.sum_eq_zero
  --   (fun i hi => sortedEigN_w0_eq_zero hGB F i (Finset.mem_Ico.1 hi).1), add_zero]
  have hs : GBᵀ = GB := transpose_eq_of_isHermitian hGB.isHermitian
  rw [trace_eq_sum_sortedEig (w0_isHermitian hs F)]
  have h1 : ∑ j : Fin n, sortedEig (W0 GB F) j =
      ∑ i ∈ Finset.range n, sortedEigN (W0 GB F) i := by
    rw [← Fin.sum_univ_eq_sum_range]; simp [sortedEigN]
  have h2 : ∑ j : Fin k, lam GB F j = ∑ i ∈ Finset.range k, sortedEigN (W0 GB F) i := by
    rw [← Fin.sum_univ_eq_sum_range]; rfl
  rw [h1, h2, ← Finset.sum_range_add_sum_Ico _ hkn, Finset.sum_eq_zero
    (fun i hi => sortedEigN_w0_eq_zero hGB F i (Finset.mem_Ico.1 hi).1), add_zero]

lemma bulk_limit_algebra (hkn : k < n) (δ2 : ℝ) (l : ℕ → ℝ) :
    ((∑ i ∈ Finset.range k, l i + δ2) - ∑ i ∈ Finset.range k, (l i + δ2 / n)) /
      ((n : ℝ) - k) = δ2 / n := by
  -- hint: rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- have hk : (k : ℝ) < n := by exact_mod_cast hkn
  -- have h1 : (n : ℝ) - k ≠ 0 := by linarith  (use `sub_ne_zero.2 hk.ne'`)
  -- have h2 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- field_simp; ring
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hk : (k : ℝ) < n := by exact_mod_cast hkn
  have h1 : (n : ℝ) - k ≠ 0 := by linarith
  have h2 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  field_simp; ring

lemma ratio_limit (hn : 0 < n) (δ2 l : ℝ) (hδ : 0 < δ2) (hl : 0 ≤ l) :
    (δ2 / n) / (l + δ2 / n) = δ2 / ((n : ℝ) * l + δ2) := by
  -- hint: have : (0 : ℝ) < n := by exact_mod_cast hn
  -- have : 0 < l + δ2 / n := by positivity
  -- field_simp; ring
  field_simp

/-! ## Corollary 1 -/

lemma trace_projB {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1) :
    (projB b).trace = k := by
  -- hint: rw [projB, Matrix.trace_mul_comm, hb, Matrix.trace_one, Fintype.card_fin]
  rw [projB, Matrix.trace_mul_comm, hb, Matrix.trace_one, Fintype.card_fin]

lemma sum_one_sub_sortedEig_gram (M : Matrix (Fin k) (Fin k) ℝ) :
    ∑ i, (1 - sortedEig (Mᵀ * M) i) = k - frobSq M := by
  -- hint: rw [Finset.sum_sub_distrib,
  --   ← trace_eq_sum_sortedEig (posSemidef_transpose_mul M).isHermitian, frobSq_eq_trace]; simp
  rw [Finset.sum_sub_distrib,
  ← trace_eq_sum_sortedEig (posSemidef_transpose_mul M).isHermitian, frobSq_eq_trace]; simp

lemma colVec_hmat {p : ℕ} (h : Fin k → EuclideanSpace ℝ (Fin p)) (j : Fin k) :
    colVec (Hmat h) j = h j := by
  -- hint: ext i; simp [colVec, Hmat]
  ext i
  simp [colVec, Hmat]

lemma colVec_transpose_mul_hmat {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ)
    (h : Fin k → EuclideanSpace ℝ (Fin p)) (j : Fin k) :
    colVec (bᵀ * Hmat h) j = Matrix.toEuclideanLin bᵀ (h j) := by
  -- hint: ext i; simp [colVec, Hmat, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
  --   Matrix.mul_apply]
  ext i
  simp [colVec, Hmat, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]

lemma frobSq_eq_sum_norm_colVec {m l : ℕ} (M : Matrix (Fin m) (Fin l) ℝ) :
    frobSq M = ∑ j, ‖colVec M j‖ ^ 2 := by
  -- hint: simp only [norm_colVec_sq_eq, frobSq, Matrix.mul_apply, Matrix.transpose_apply, sq]
  -- exact Finset.sum_comm
  simp only [norm_colVec_sq_eq, Matrix.mul_apply, Matrix.transpose_apply]
  unfold frobSq
  rw [Finset.sum_comm]
  simp only [sq]

lemma norm_projB_eq {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (u : EuclideanSpace ℝ (Fin p)) :
    ‖Matrix.toEuclideanLin (projB b) u‖ = ‖Matrix.toEuclideanLin bᵀ u‖ := by
  -- hint: rw [projB, toEuclideanLin_mul]; exact norm_toEuclideanLin_of_orthonormal b hb _
  -- (`toEuclideanLin_mul` may need `LinearMap.comp_apply` afterwards)
  rw [projB, toEuclideanLin_mul]
  exact norm_toEuclideanLin_of_orthonormal b hb _

lemma sum_norm_projB_sq {p : ℕ} (b : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (h : Fin k → EuclideanSpace ℝ (Fin p)) :
    ∑ j, ‖Matrix.toEuclideanLin (projB b) (h j)‖ ^ 2 = frobSq (bᵀ * Hmat h) := by
  -- hint: rw [frobSq_eq_sum_norm_colVec]; simp only [colVec_transpose_mul_hmat, norm_projB_eq b hb]
  rw [frobSq_eq_sum_norm_colVec]
  simp only [colVec_transpose_mul_hmat, norm_projB_eq b hb]

lemma frobSq_proj_sub {p : ℕ} (b H : Matrix (Fin p) (Fin k) ℝ) (hb : bᵀ * b = 1)
    (hH : Hᵀ * H = 1) :
    frobSq (H * Hᵀ - b * bᵀ) = 2 * k - 2 * frobSq (bᵀ * H) := by
  -- hint: rw [frobSq_eq_trace, frobSq_eq_trace]
  -- simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
  --   Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  -- each of the four traces: move factors with `Matrix.trace_mul_comm`/`Matrix.trace_mul_cycle`
  -- and use `hb`, `hH` (`H * Hᵀ * (H * Hᵀ)` has trace `k`, likewise for `b`;
  -- `tr(H Hᵀ b bᵀ) = tr(b bᵀ H Hᵀ) = tr(Hᵀ b bᵀ H)`), then `Matrix.trace_one`; `ring`
  have a1 : (H * Hᵀ * (H * Hᵀ)).trace = k := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Hᵀ H, hH, Matrix.one_mul, Matrix.trace_mul_comm, hH,
      Matrix.trace_one, Fintype.card_fin]
  have a2 : (b * bᵀ * (b * bᵀ)).trace = k := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc bᵀ b, hb, Matrix.one_mul, Matrix.trace_mul_comm, hb,
      Matrix.trace_one, Fintype.card_fin]
  have a3 : (H * Hᵀ * (b * bᵀ)).trace = (Hᵀ * b * (bᵀ * H)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm H]
    simp only [Matrix.mul_assoc]
  have a4 : (b * bᵀ * (H * Hᵀ)).trace = (Hᵀ * b * (bᵀ * H)).trace := by
    rw [Matrix.trace_mul_comm (b * bᵀ) (H * Hᵀ), a3]
  rw [frobSq_eq_trace, frobSq_eq_trace]
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  rw [a1, a2, a3, a4]
  ring

end PCError

end

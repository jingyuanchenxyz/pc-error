import LatentError.Lemmas.Basic

/-!
# Spectral helper lemmas: sorted spectra via characteristic polynomials, Gram duality

`sortedEigN A` is read off the sorted root list of `A.charpoly`; multiplying the
characteristic polynomial by `X^l` appends `l` zeros, which is how the padded spectra of
`A Aᵀ` and `Aᵀ A` are compared (`Matrix.charpoly_mul_comm'`).
-/

open scoped Matrix Topology MatrixOrder
open Filter Polynomial

noncomputable section

namespace PCError

/-- The roots of the characteristic polynomial, sorted in weakly decreasing order. -/
def rootList {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : List ℝ :=
  A.charpoly.roots.sort (fun x y => x ≥ y)

lemma ofFn_sortedEig {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) :
    List.ofFn (sortedEig A) = rootList A := by
  have hmap : Multiset.map (⇑(RCLike.re : ℝ →+ ℝ)) A.charpoly.roots = A.charpoly.roots := by
    simp
  have key := hA.sort_roots_charpoly_eq_eigenvalues₀
  rw [hmap] at key
  rw [rootList, key, List.ofFn_congr (Fintype.card_fin m)]
  congr 1
  funext j
  simp [sortedEig, hA]

lemma length_rootList {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) :
    (rootList A).length = m := by
  rw [← ofFn_sortedEig hA, List.length_ofFn]

lemma sortedEigN_eq_getD {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) (j : ℕ) :
    sortedEigN A j = (rootList A).getD j 0 := by
  rw [← ofFn_sortedEig hA, sortedEigN]
  split_ifs with hj
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma sort_add_replicate_zero (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) (l : ℕ) :
    (s + Multiset.replicate l 0).sort (fun x y => x ≥ y) =
      s.sort (fun x y => x ≥ y) ++ List.replicate l 0 := by
  apply List.Perm.eq_of_sortedGE
  · exact List.sortedGE_iff_pairwise.2 (Multiset.pairwise_sort _ _)
  · rw [List.sortedGE_iff_pairwise, List.pairwise_append]
    refine ⟨Multiset.pairwise_sort _ _, List.pairwise_replicate.2 (Or.inr le_rfl), ?_⟩
    intro a ha b hb
    rw [List.eq_of_mem_replicate hb]
    exact hs a ((Multiset.mem_sort _).1 ha)
  · rw [← Multiset.coe_eq_coe, ← Multiset.coe_add, Multiset.sort_eq, Multiset.sort_eq,
      Multiset.coe_replicate]

lemma getD_append_replicate_zero (L : List ℝ) (l j : ℕ) :
    (L ++ List.replicate l 0).getD j 0 = L.getD j 0 := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · push_neg at hj
    rw [List.getD_append_right _ _ _ _ hj, List.getD_eq_default _ _ hj]
    by_cases hj' : j - L.length < l
    · exact List.getD_replicate _ hj'
    · exact List.getD_eq_default _ _ (by simp; omega)

lemma roots_X_pow_mul_charpoly {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (l : ℕ) :
    ((X : ℝ[X]) ^ l * A.charpoly).roots = A.charpoly.roots + Multiset.replicate l 0 := by
  rw [roots_mul ((monic_X_pow l).mul A.charpoly_monic).ne_zero, roots_X_pow,
    Multiset.nsmul_singleton, add_comm]

lemma roots_charpoly_nonneg {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.PosSemidef) :
    ∀ x ∈ A.charpoly.roots, 0 ≤ x := by
  intro x hx
  rw [hA.isHermitian.roots_charpoly_eq_eigenvalues] at hx
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hx
  simpa using hA.eigenvalues_nonneg i

lemma posSemidef_mul_transpose {m l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ) :
    (A * Aᵀ).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose A

lemma posSemidef_transpose_mul {m l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ) :
    (Aᵀ * A).PosSemidef := by
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self A

/-- Padded sorted spectra of `A Aᵀ` and `Aᵀ A` agree. -/
theorem sortedEigN_mul_transpose {m l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ) :
    sortedEigN (A * Aᵀ) = sortedEigN (Aᵀ * A) := by
  have h1 := posSemidef_mul_transpose A
  have h2 := posSemidef_transpose_mul A
  have key : rootList (A * Aᵀ) ++ List.replicate l 0 =
      rootList (Aᵀ * A) ++ List.replicate m 0 := by
    have hc := Matrix.charpoly_mul_comm' A Aᵀ
    simp only [Fintype.card_fin] at hc
    rw [rootList, rootList, ← sort_add_replicate_zero _ (roots_charpoly_nonneg h1),
      ← sort_add_replicate_zero _ (roots_charpoly_nonneg h2),
      ← roots_X_pow_mul_charpoly, ← roots_X_pow_mul_charpoly, hc]
  funext j
  rw [sortedEigN_eq_getD h1.isHermitian, sortedEigN_eq_getD h2.isHermitian,
    ← getD_append_replicate_zero (rootList (A * Aᵀ)) l j, key, getD_append_replicate_zero]

/-- Gram duality for eigenvectors: `v ↦ Aᵀ v/√λ`. -/
theorem gram_eigvec {m l : ℕ} (A : Matrix (Fin m) (Fin l) ℝ) (v : EuclideanSpace ℝ (Fin m))
    (lam : ℝ) (hlam : lam ≠ 0) (hv : IsUnitEigvec (A * Aᵀ) v lam) :
    IsUnitEigvec (Aᵀ * A) ((1 / Real.sqrt lam) • Matrix.toEuclideanLin Aᵀ v) lam := by
  obtain ⟨hvn, hveq⟩ := hv
  have hnorm : ‖Matrix.toEuclideanLin Aᵀ v‖ ^ 2 = lam := by
    rw [norm_toEuclideanLin_sq, Matrix.transpose_transpose, hveq, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hvn]
    ring
  have hpos : 0 < lam := lt_of_le_of_ne (hnorm ▸ sq_nonneg _) (Ne.symm hlam)
  refine ⟨?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ← Real.sqrt_sq (norm_nonneg (Matrix.toEuclideanLin Aᵀ v)), hnorm]
    field_simp
  · rw [map_smul, toEuclideanLin_mul, ← toEuclideanLin_mul A, hveq, map_smul, smul_comm]

/-! ## Sorted eigenvalues and eigenvectors -/

lemma sortedEig_of_isHermitian {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian)
    (j : Fin m) : sortedEig A j = hA.eigenvalues₀ (Fin.cast (Fintype.card_fin m).symm j) := by
  simp [sortedEig, hA]

lemma sortedEig_antitone {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) : Antitone (sortedEig A) := by
  by_cases hA : A.IsHermitian
  · intro i j hij
    rw [sortedEig_of_isHermitian hA, sortedEig_of_isHermitian hA]
    exact hA.eigenvalues₀_antitone hij
  · intro i j _
    simp [sortedEig, hA]

/-- The symmetric operator attached to a Hermitian matrix. -/
lemma isSymmetric_of_isHermitian {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) :
    (Matrix.toEuclideanLin A).IsSymmetric :=
  Matrix.isHermitian_iff_isSymmetric.1 hA

lemma eigenvalues₀_eq {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian) :
    hA.eigenvalues₀ = (isSymmetric_of_isHermitian hA).eigenvalues finrank_euclideanSpace :=
  rfl

/-- Every sorted eigenvalue has a unit eigenvector. -/
lemma exists_unitEigvec_sortedEig {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian)
    (j : Fin m) : ∃ v, IsUnitEigvec A v (sortedEig A j) := by
  set hT := isSymmetric_of_isHermitian hA
  set i := Fin.cast (Fintype.card_fin m).symm j
  refine ⟨hT.eigenvectorBasis finrank_euclideanSpace i, ?_, ?_⟩
  · exact (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.1 i
  · rw [sortedEig_of_isHermitian hA, eigenvalues₀_eq]
    exact (hT.hasEigenvector_eigenvectorBasis finrank_euclideanSpace i).apply_eq_smul

/-- Every eigenvalue is a sorted eigenvalue. -/
lemma exists_sortedEig_eq {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian)
    {v : EuclideanSpace ℝ (Fin m)} {μ : ℝ} (hv : IsUnitEigvec A v μ) :
    ∃ i, sortedEig A i = μ := by
  have hv0 : v ≠ 0 := by rintro rfl; simp [IsUnitEigvec] at hv
  have hμ : Module.End.HasEigenvalue (Matrix.toEuclideanLin A) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 hv.2, hv0⟩
  obtain ⟨i, hi⟩ := (isSymmetric_of_isHermitian hA).exists_eigenvalues_eq
    finrank_euclideanSpace hμ
  refine ⟨Fin.cast (Fintype.card_fin m) i, ?_⟩
  rw [sortedEig_of_isHermitian hA, eigenvalues₀_eq]
  simpa using hi

/-- A simple sorted eigenvalue has, up to sign, a unique unit eigenvector. -/
lemma unitEigvec_eq_or_eq_neg {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian)
    {j : Fin m} (hsimple : ∀ i, i ≠ j → sortedEig A i ≠ sortedEig A j)
    {v w : EuclideanSpace ℝ (Fin m)} (hv : IsUnitEigvec A v (sortedEig A j))
    (hw : IsUnitEigvec A w (sortedEig A j)) : w = v ∨ w = -v := by
  set T := Matrix.toEuclideanLin A
  set hT := isSymmetric_of_isHermitian hA
  set μ := sortedEig A j
  have hv0 : v ≠ 0 := by rintro rfl; simp [IsUnitEigvec] at hv
  have hvmem : v ∈ Module.End.eigenspace T μ := Module.End.mem_eigenspace_iff.2 hv.2
  have hwmem : w ∈ Module.End.eigenspace T μ := Module.End.mem_eigenspace_iff.2 hw.2
  have hμ : Module.End.HasEigenvalue T μ :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨hvmem, hv0⟩
  have hcard := hT.card_filter_eigenvalues_eq finrank_euclideanSpace hμ
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hcard
  have hone : Finset.card {i | hT.eigenvalues finrank_euclideanSpace i = μ} = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨Fin.cast (Fintype.card_fin m).symm j, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      have : sortedEig A (Fin.cast (Fintype.card_fin m) i) = μ := by
        rw [sortedEig_of_isHermitian hA, eigenvalues₀_eq]; simpa using hi
      by_contra hne
      exact hsimple _ (fun h => hne (by ext; simp [← h])) this
    · rintro rfl
      rw [← eigenvalues₀_eq hA]
      exact (sortedEig_of_isHermitian hA j).symm
  rw [hone] at hcard
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hvmem⟩ : Module.End.eigenspace T μ)
    (by simpa using hv0)).1 hcard.symm ⟨w, hwmem⟩
  have hcw : c • v = w := by simpa using congrArg Subtype.val hc
  have habs : |c| = 1 := by
    have := congrArg norm hcw
    rwa [norm_smul, hv.1, hw.1, mul_one, Real.norm_eq_abs] at this
  rcases abs_eq (zero_le_one' ℝ) |>.1 habs with h | h
  · left; rw [← hcw, h, one_smul]
  · right; rw [← hcw, h, neg_one_smul]

/-! ## Operator norm and Weyl's inequality in `sortedEig` form -/

lemma norm_toEuclideanLin_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) : ‖Matrix.toEuclideanLin M x‖ ≤ opNorm M * ‖x‖ := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) M).le_opNorm x

lemma opNorm_nonneg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) : 0 ≤ opNorm M := norm_nonneg _

lemma continuous_opNorm {m : ℕ} : Continuous (fun M : Matrix (Fin m) (Fin m) ℝ => opNorm M) := by
  open scoped Matrix.Norms.L2Operator in
  have h : (fun M : Matrix (Fin m) (Fin m) ℝ => opNorm M) = fun M => ‖M‖ := by
    funext M; exact Matrix.l2_opNorm_toEuclideanCLM M
  open scoped Matrix.Norms.L2Operator in
  rw [h]
  open scoped Matrix.Norms.L2Operator in
  exact continuous_norm

lemma tendsto_opNorm_sub {m : ℕ} {ι : Type*} {L : Filter ι}
    {A : ι → Matrix (Fin m) (Fin m) ℝ} {Ainf : Matrix (Fin m) (Fin m) ℝ}
    (h : Tendsto A L (𝓝 Ainf)) : Tendsto (fun p => opNorm (A p - Ainf)) L (𝓝 0) := by
  have h0 : opNorm (0 : Matrix (Fin m) (Fin m) ℝ) = 0 := by rw [opNorm, map_zero, norm_zero]
  have := (continuous_opNorm.tendsto (0 : Matrix (Fin m) (Fin m) ℝ)).comp
    (tendsto_sub_nhds_zero_iff.2 h)
  rw [h0] at this
  exact this

/-- Weyl's inequality (Fact 2) for the sorted eigenvalues `sortedEig`. -/
lemma sortedEig_sub_le {m : ℕ} (hFact2 : Fact2_Weyl m) {A B : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (i : Fin m) :
    |sortedEig B i - sortedEig A i| ≤ opNorm (B - A) := by
  let e : Fin m ≃ Fin m :=
    (finCongr (Fintype.card_fin m).symm).trans (Fintype.equivOfCardEq (Fintype.card_fin _))
  have hsA : sortedEig A = fun i => hA.eigenvalues (e i) := by
    funext i; simp [sortedEig_of_isHermitian hA, Matrix.IsHermitian.eigenvalues, e]
  have hsB : sortedEig B = fun i => hB.eigenvalues (e i) := by
    funext i; simp [sortedEig_of_isHermitian hB, Matrix.IsHermitian.eigenvalues, e]
  exact hFact2 A B hA hB (sortedEig A) (sortedEig B) e e (sortedEig_antitone A)
    (sortedEig_antitone B) hsA hsB i

/-- Weyl ⇒ sorted eigenvalues are continuous along convergent sequences. -/
lemma tendsto_sortedEig {m : ℕ} (hFact2 : Fact2_Weyl m) {ι : Type*} {L : Filter ι}
    {A : ι → Matrix (Fin m) (Fin m) ℝ} {Ainf : Matrix (Fin m) (Fin m) ℝ}
    (hA : ∀ p, (A p).IsHermitian) (hAinf : Ainf.IsHermitian) (h : Tendsto A L (𝓝 Ainf))
    (i : Fin m) : Tendsto (fun p => sortedEig (A p) i) L (𝓝 (sortedEig Ainf i)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) (tendsto_opNorm_sub h)
  rw [Real.norm_eq_abs]
  exact sortedEig_sub_le hFact2 hAinf (hA p) i

end PCError

end

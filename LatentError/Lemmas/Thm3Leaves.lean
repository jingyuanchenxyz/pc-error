import LatentError.Lemmas.HardLeaves

/-!
# Leaf lemmas for Theorem 3 (rotation error is not estimable)

* `sinSq_nlim_indep`: for a fixed admissible `Σ`, the angle `sin²∠(νⱼ, eⱼ)` does not depend
  on the eigenbasis `V` of `K(Σ)` or on the sign of `νⱼ` (both are unique up to sign; the
  comparison goes through the dual eigenvector `Φ̄^∞ wⱼ / √(nλⱼ)`).
* `exists_orthogonal_diag`: a Householder reflection `R` with prescribed `R j j ∈ [0, 1]`.
* `exists_sigma_sinSq`: with `O := R Uᵀ` (`U` an eigenbasis of `M̂`), Lemma 6 gives
  `N(Σ_O) = O M̂ Oᵀ`, whose `j`-th eigenvector is `R eⱼ`, so the rotation error is `1 − R j j²`.
-/

open Filter
open scoped Topology Matrix MatrixOrder

noncomputable section

namespace PCError

variable {k n : ℕ}

/-- The `j`-th coordinate of `Φ̄^∞ w`. -/
lemma inner_phiBarInf_e (Sig GB V : Matrix (Fin k) (Fin k) ℝ) (F : Matrix (Fin k) (Fin n) ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (j : Fin k) :
    inner ℝ (Matrix.toEuclideanLin (PhiBarInf Sig GB V F) w) (e j) =
      Real.sqrt (sortedEig (Kmat Sig GB) j) *
        ∑ i, V i j * ((((CFC.sqrt Sig)⁻¹ * F) *ᵥ (WithLp.ofLp w)) i) := by
  simp [PhiBarInf, e, Matrix.toLpLin_apply, EuclideanSpace.inner_single_right, Matrix.mul_assoc,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  left
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

lemma inner_colVec_e (R : Matrix (Fin k) (Fin k) ℝ) (j : Fin k) :
    inner ℝ (colVec R j) (e j) = R j j := by
  simp [colVec, e, EuclideanSpace.inner_single_right]


section indep

variable {GB : Matrix (Fin k) (Fin k) ℝ} {F : Matrix (Fin k) (Fin n) ℝ}

lemma lt_of_assumption6 (hA6 : Assumption6 GB F) (j : Fin k) : (j : ℕ) < n := by
  by_contra h
  have := hA6.2 j
  simp [lam, sortedEigN, h] at this

lemma nlim_simple {Sig V : Matrix (Fin k) (Fin k) ℝ} (hSig : Sig.PosDef)
    (hA5 : Assumption5 Sig GB) (hV : IsEigenbasis (Kmat Sig GB) V) (hA6 : Assumption6 GB F)
    (j : Fin k) : ∀ i, i ≠ j → sortedEig (Nlim Sig GB V F) i ≠ sortedEig (Nlim Sig GB V F) j := by
  intro i hi
  rw [sortedEig_nlim hSig hA5 hV, sortedEig_nlim hSig hA5 hV]
  exact hA6.1.injective.ne hi

lemma sinSq_nlim_eq_w0 (hA6 : Assumption6 GB F) {Sig V : Matrix (Fin k) (Fin k) ℝ}
    (hSig : Sig.PosDef) (hA5 : Assumption5 Sig GB) (hV : IsEigenbasis (Kmat Sig GB) V)
    (j : Fin k) {w : EuclideanSpace ℝ (Fin n)} (hw : IsUnitEigvec (W0 GB F) w (lam GB F j))
    {ν : EuclideanSpace ℝ (Fin k)}
    (hν : IsUnitEigvec (Nlim Sig GB V F) ν (sortedEig (Nlim Sig GB V F) j)) :
    sinSq ν (e j) = 1 - (1 / ((n : ℝ) * lam GB F j)) * sortedEig (Kmat Sig GB) j *
      (∑ i, V i j * ((((CFC.sqrt Sig)⁻¹ * F) *ᵥ (WithLp.ofLp w)) i)) ^ 2 := by
  have hl := hA6.2 j
  have hv : IsUnitEigvec (Nlim Sig GB V F)
      ((1 / Real.sqrt ((n : ℝ) * lam GB F j)) •
        Matrix.toEuclideanLin (PhiBarInf Sig GB V F) w) (sortedEig (Nlim Sig GB V F) j) := by
    rw [sortedEig_nlim hSig hA5 hV F j]
    exact nlim_eigvec_of_w0 hSig hA5 hV F hl hw
  have hpm := unitEigvec_eq_or_eq_neg (nlim_isHermitian F) (nlim_simple hSig hA5 hV hA6 j) hv hν
  rw [sinSq_eq_of_eq_or_neg hpm, sinSq_of_unit hv.1 (by simp [e]), real_inner_smul_left,
    inner_phiBarInf_e]
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (n_pos_of_assumption6 hA6 j)
  have hμ : 0 ≤ sortedEig (Kmat Sig GB) j := (hA5.2 j).le
  have hnl : 0 ≤ (n : ℝ) * lam GB F j := by positivity
  rw [mul_pow, mul_pow, div_pow, one_pow, Real.sq_sqrt hnl, Real.sq_sqrt hμ]
  ring

/-- The angle `sin²∠(νⱼ, eⱼ)` depends only on `Σ`, not on the eigenbasis `V` of `K(Σ)` or on
the unit eigenvector `νⱼ` of `N`. -/
lemma sinSq_nlim_indep (hGB : GB.PosDef) (hA6 : Assumption6 GB F)
    {Sig V V' : Matrix (Fin k) (Fin k) ℝ} (hSig : Sig.PosDef) (hA5 : Assumption5 Sig GB)
    (hV : IsEigenbasis (Kmat Sig GB) V) (hV' : IsEigenbasis (Kmat Sig GB) V') (j : Fin k)
    {ν ν' : EuclideanSpace ℝ (Fin k)}
    (hν : IsUnitEigvec (Nlim Sig GB V F) ν (sortedEig (Nlim Sig GB V F) j))
    (hν' : IsUnitEigvec (Nlim Sig GB V' F) ν' (sortedEig (Nlim Sig GB V' F) j)) :
    sinSq ν (e j) = sinSq ν' (e j) := by
  have hjn := lt_of_assumption6 hA6 j
  have hs := transpose_eq_of_isHermitian hGB.isHermitian
  obtain ⟨w, hw⟩ := exists_unitEigvec_sortedEig (w0_isHermitian hs F) ⟨j, hjn⟩
  rw [← sortedEigN_fin _ _ hjn, ← lam] at hw
  rw [sinSq_nlim_eq_w0 hA6 hSig hA5 hV j hw hν, sinSq_nlim_eq_w0 hA6 hSig hA5 hV' j hw hν']
  have hsK : ∀ i, i ≠ j → sortedEig (Kmat Sig GB) i ≠ sortedEig (Kmat Sig GB) j :=
    fun i hi => hA5.1.injective.ne hi
  rcases unitEigvec_eq_or_eq_neg (kmat_isHermitian hs) hsK (hV.isUnitEigvec j)
    (hV'.isUnitEigvec j) with h | h
  · have hc : ∀ i, V' i j = V i j := fun i => by
      simpa [colVec] using congrArg (fun x : EuclideanSpace ℝ (Fin k) => x i) h
    simp only [hc]
  · have hc : ∀ i, V' i j = -V i j := fun i => by
      simpa [colVec] using congrArg (fun x : EuclideanSpace ℝ (Fin k) => x i) h
    simp only [hc, neg_mul, Finset.sum_neg_distrib, neg_sq]

end indep

/-- A Householder reflection with a prescribed diagonal entry in `[0, 1]` (needs `k ≥ 2`). -/
lemma exists_orthogonal_diag (hk : 2 ≤ k) (j : Fin k) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∃ R : Matrix (Fin k) (Fin k) ℝ, Rᵀ * R = 1 ∧ R * Rᵀ = 1 ∧ R j j = c := by
  obtain ⟨j', hj'⟩ : ∃ j' : Fin k, j' ≠ j := by
    by_cases h : (j : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by rw [Fin.ext_iff] at h'; simp at h'; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h (by rw [Fin.ext_iff] at h'; simp at h'; omega)⟩
  have ha : 0 ≤ (1 - c) / 2 := by linarith
  have hb : 0 ≤ (1 + c) / 2 := by linarith
  set u : Fin k → ℝ := fun i =>
    if i = j then Real.sqrt ((1 - c) / 2) else if i = j' then Real.sqrt ((1 + c) / 2) else 0
    with hu_def
  have hu : u ⬝ᵥ u = 1 := by
    have : ∀ i, u i * u i = (if i = j then (1 - c) / 2 else 0) +
        (if i = j' then (1 + c) / 2 else 0) := by
      intro i
      by_cases h1 : i = j
      · subst h1
        simp only [hu_def, ↓reduceIte, hj'.symm, add_zero]
        exact Real.mul_self_sqrt ha
      · by_cases h2 : i = j'
        · subst h2
          simp only [hu_def, ↓reduceIte, h1, zero_add]
          exact Real.mul_self_sqrt hb
        · simp only [hu_def, h1, h2, ↓reduceIte, add_zero, mul_zero]
    simp only [dotProduct, this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    ring
  set R : Matrix (Fin k) (Fin k) ℝ := 1 - (2 : ℝ) • Matrix.vecMulVec u u with hR
  have hRt : Rᵀ = R := by
    simp [hR, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_vecMulVec]
  have hRR : R * R = 1 := by
    simp only [hR, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.vecMulVec_mul_vecMulVec, hu, one_smul, smul_smul]
    rw [show (2 : ℝ) * 2 = 2 + 2 by norm_num, add_smul]
    abel
  refine ⟨R, by rw [hRt, hRR], by rw [hRt, hRR], ?_⟩
  simp only [hR, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply,
    Matrix.vecMulVec_apply, hu_def, ↓reduceIte, smul_eq_mul]
  rw [Real.mul_self_sqrt ha]
  ring

/-- Theorem 3(ii), attainment: for every `t ∈ [0, 1]` some admissible `Σ` has rotation error
exactly `t`, for every eigenbasis `V` and every unit eigenvector `νⱼ`. -/
lemma exists_sigma_sinSq (hk : 2 ≤ k) {Sf GB : Matrix (Fin k) (Fin k) ℝ} (hSf : Sf.PosDef)
    (hGB : GB.PosDef) (hA5 : Assumption5 Sf GB) {F : Matrix (Fin k) (Fin n) ℝ}
    (hA6 : Assumption6 GB F) (j : Fin k) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Sig : Matrix (Fin k) (Fin k) ℝ, Admissible Sf GB Sig ∧
      (∃ (V : Matrix (Fin k) (Fin k) ℝ) (ν : EuclideanSpace ℝ (Fin k)),
        IsEigenbasis (Kmat Sig GB) V ∧
        IsUnitEigvec (Nlim Sig GB V F) ν (sortedEig (Nlim Sig GB V F) j)) ∧
      ∀ (V : Matrix (Fin k) (Fin k) ℝ) (ν : EuclideanSpace ℝ (Fin k)),
        IsEigenbasis (Kmat Sig GB) V →
        IsUnitEigvec (Nlim Sig GB V F) ν (sortedEig (Nlim Sig GB V F) j) →
        sinSq ν (e j) = t := by
  obtain ⟨U, hU⟩ := exists_isEigenbasis (isHermitian_of_transpose_eq (mhat_transpose GB F))
  have hc1 : Real.sqrt (1 - t) ≤ 1 :=
    calc Real.sqrt (1 - t) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt (by linarith [ht.1])
      _ = 1 := Real.sqrt_one
  obtain ⟨R, hRtR, hRRt, hRjj⟩ := exists_orthogonal_diag hk j (Real.sqrt_nonneg (1 - t)) hc1
  have hO : R * Uᵀ ∈ Matrix.orthogonalGroup (Fin k) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hU.1, Matrix.one_mul, hRRt]
  obtain ⟨V0, hV0, hN⟩ := exists_eigenbasis_nlim_sigmaO hSf hGB hA5 F hO
  have hadm := sigmaO_admissible hSf hGB hA5 hO
  have hA5' : Assumption5 (SigmaO GB (LamDiag Sf GB) (R * Uᵀ)) GB := by
    unfold Assumption5
    rw [hadm.2]
    exact hA5
  have hMR : R * Uᵀ * Mhat GB F * (R * Uᵀ)ᵀ * R =
      R * Matrix.diagonal (sortedEig (Mhat GB F)) := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [hRtR, Matrix.mul_one, hU.2, ← Matrix.mul_assoc Uᵀ U, hU.1, Matrix.one_mul]
  have hspec : sortedEig (R * Uᵀ * Mhat GB F * (R * Uᵀ)ᵀ) = sortedEig (Mhat GB F) :=
    sortedEig_eq_of_mul_eq hRtR (sortedEig_antitone _) hMR
  have hRe : IsEigenbasis (R * Uᵀ * Mhat GB F * (R * Uᵀ)ᵀ) R := ⟨hRtR, by rw [hspec]; exact hMR⟩
  have hν0 : IsUnitEigvec (Nlim (SigmaO GB (LamDiag Sf GB) (R * Uᵀ)) GB V0 F) (colVec R j)
      (sortedEig (Nlim (SigmaO GB (LamDiag Sf GB) (R * Uᵀ)) GB V0 F) j) := by
    rw [hN]
    exact hRe.isUnitEigvec j
  have hval : sinSq (colVec R j) (e j) = t := by
    rw [sinSq_of_unit hν0.1 (by simp [e]), inner_colVec_e, hRjj,
      Real.sq_sqrt (by linarith [ht.2])]
    ring
  refine ⟨_, hadm, ⟨V0, colVec R j, hV0, hν0⟩, fun V ν hV hν => ?_⟩
  rw [sinSq_nlim_indep hGB hA6 hadm.1 hA5' hV hV0 j hν hν0, hval]

end PCError

end

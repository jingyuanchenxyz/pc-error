import LatentError.Facts.Weyl
import LatentError.Lemmas.Convergence

/-!
# Fact 3: eigenvector continuity at a simple eigenvalue

Fact 3 is never used by any proof in this development (Lemma 2 is proved from Weyl and
compactness of the sphere, as in the paper), but the frozen statements carry it as a
hypothesis, so we prove it too — from Weyl (`fact2_weyl`) and the eigenpair convergence of
Lemma 2 (`eigpair_convergence`).

Given `A p → A∞` symmetric and a simple eigenvalue `μ` of `A∞` with unit eigenvector `v`:
`μ` is the `j`-th sorted eigenvalue for some `j`, that index is simple, and Lemma 2 gives
unit eigenvectors `w p` of `A p` at the `j`-th sorted eigenvalue with `|⟪w p, v⟫| → 1`.
Pinning the sign (`sign_pinning`) gives `v' p → v` with `⟪v' p, v⟫ ≥ 0`.
-/

open Filter
open scoped Topology

noncomputable section

namespace PCError

/-- **Fact 3, proved.** -/
theorem fact3_eigCont (m : ℕ) : Fact3_EigCont m := by
  classical
  intro A Ainf hA hAinf hlim μ v hv1 hv2 hsimple
  have hvunit : IsUnitEigvec Ainf v μ := ⟨hv1, hv2⟩
  obtain ⟨j, hj⟩ := exists_sortedEig_eq hAinf hvunit
  -- the index `j` is simple: two orthogonal unit eigenvectors would both be `± v`
  have hsimplej : ∀ i, i ≠ j → sortedEig Ainf i ≠ sortedEig Ainf j := by
    intro i hij hEq
    have hbi : IsUnitEigvec Ainf (eigBasis hAinf i) μ :=
      ⟨(eigBasis hAinf).orthonormal.1 i, by
        rw [toEuclideanLin_eigBasis hAinf i, hEq, hj]⟩
    have hbj : IsUnitEigvec Ainf (eigBasis hAinf j) μ :=
      ⟨(eigBasis hAinf).orthonormal.1 j, by rw [toEuclideanLin_eigBasis hAinf j, hj]⟩
    have horth : (inner ℝ (eigBasis hAinf i) (eigBasis hAinf j) : ℝ) = 0 :=
      (eigBasis hAinf).orthonormal.2 hij
    have hvv : (inner ℝ v v : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, hv1]
      norm_num
    rcases hsimple _ hbi.1 hbi.2 with h1 | h1 <;> rcases hsimple _ hbj.1 hbj.2 with h2 | h2 <;>
      rw [h1, h2] at horth <;>
      simp only [inner_neg_left, inner_neg_right, hvv, neg_neg] at horth <;>
      norm_num at horth
  -- unit eigenvectors of `A p` at the `j`-th sorted eigenvalue
  have hex : ∀ p, ∃ u, IsUnitEigvec (A p) u (sortedEig (A p) j) :=
    fun p => exists_unitEigvec_sortedEig (hA p) j
  set w : ℕ → EuclideanSpace ℝ (Fin m) := fun p => Classical.choose (hex p) with hwdef
  have hw : ∀ p, IsUnitEigvec (A p) (w p) (sortedEig (A p) j) := fun p => Classical.choose_spec (hex p)
  have hconv := eigpair_convergence (fact2_weyl m) A Ainf hA hAinf hlim j hsimplej v
    (by rw [hj]; exact hvunit)
  have habs : Tendsto (fun p => |inner ℝ (w p) v|) atTop (𝓝 1) :=
    hconv.2.2 w (Eventually.of_forall fun p => hw p)
  obtain ⟨hne, hten⟩ := sign_pinning w v (fun p => (hw p).1) hv1 habs
  refine ⟨fun p => sortedEig (A p) j, fun p => Real.sign (inner ℝ (w p) v) • w p, ?_, ?_, hten⟩
  · filter_upwards [hne] with p hp
    have hsign : Real.sign (inner ℝ (w p) v : ℝ) = 1 ∨
        Real.sign (inner ℝ (w p) v : ℝ) = -1 := by
      rcases lt_or_gt_of_ne hp with h | h
      · exact Or.inr (Real.sign_of_neg h)
      · exact Or.inl (Real.sign_of_pos h)
    refine ⟨?_, ?_, ?_⟩
    · rw [map_smul, (hw p).2, smul_comm]
    · rcases hsign with h | h <;> rw [h] <;> simp [(hw p).1]
    · rw [real_inner_smul_left]
      rcases lt_or_gt_of_ne hp with h | h
      · rw [Real.sign_of_neg h]
        nlinarith
      · rw [Real.sign_of_pos h]
        nlinarith
  · rw [← hj]
    exact hconv.2.1

end PCError

end

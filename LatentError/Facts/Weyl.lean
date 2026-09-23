import LatentError.Lemmas.Spectral

/-!
# Fact 2: Weyl's eigenvalue perturbation inequality

`mathlib` has the spectral theorem for Hermitian matrices, with the eigenvalues in weakly
decreasing order (`Matrix.IsHermitian.eigenvalues₀`, our `sortedEig`), but no
Courant–Fischer min–max theorem.  This file builds the two halves of min–max that Weyl's
inequality needs, and deduces `Fact2_Weyl`.

* `quad A x = ⟪x, A x⟫` is the quadratic form.  In the eigenbasis it is
  `∑ i, λ i * (coordinate i)²` (`quad_eq_sum`).
* On the span of the first `k+1` eigenvectors, `quad A x ≥ λ k ‖x‖²` (`quad_ge_of_upper`);
  on the vectors whose first `k` coordinates vanish, `quad A x ≤ λ k ‖x‖²`
  (`quad_le_of_lower`).
* A dimension count gives a unit vector in the first subspace for `A` whose first `k`
  coordinates for `A'` vanish; comparing the two bounds on it gives Weyl.
-/

open Matrix Finset
open scoped Topology

noncomputable section

namespace PCError

variable {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ}

/-- The quadratic form `x ↦ ⟪x, A x⟫` of a matrix. -/
def quad (A : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  inner ℝ x (Matrix.toEuclideanLin A x)

lemma quad_sub (A B : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    quad (A - B) x = quad A x - quad B x := by
  simp [quad, toEuclideanLin_sub_apply, inner_sub_right]

/-- The quadratic form is bounded by the operator norm. -/
lemma abs_quad_le (B : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    |quad B x| ≤ opNorm B * ‖x‖ ^ 2 := by
  calc |quad B x| ≤ ‖x‖ * ‖Matrix.toEuclideanLin B x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (opNorm B * ‖x‖) := by
        gcongr
        exact norm_toEuclideanLin_le B x
    _ = opNorm B * ‖x‖ ^ 2 := by ring

/-- The orthonormal eigenbasis of a Hermitian matrix, indexed so that the `i`-th vector
belongs to the `i`-th *sorted* eigenvalue. -/
def eigBasis (hA : A.IsHermitian) : OrthonormalBasis (Fin m) ℝ (EuclideanSpace ℝ (Fin m)) :=
  ((isSymmetric_of_isHermitian hA).eigenvectorBasis finrank_euclideanSpace).reindex
    (finCongr (Fintype.card_fin m))

lemma toEuclideanLin_eigBasis (hA : A.IsHermitian) (i : Fin m) :
    Matrix.toEuclideanLin A (eigBasis hA i) = sortedEig A i • eigBasis hA i := by
  rw [eigBasis, OrthonormalBasis.reindex_apply, sortedEig_of_isHermitian hA, eigenvalues₀_eq]
  have := (isSymmetric_of_isHermitian hA).apply_eigenvectorBasis finrank_euclideanSpace
    ((finCongr (Fintype.card_fin m)).symm i)
  simpa using this

/-- Coordinates of `A x` in the eigenbasis. -/
lemma repr_toEuclideanLin (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    (eigBasis hA).repr (Matrix.toEuclideanLin A x) i =
      sortedEig A i * (eigBasis hA).repr x i := by
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply,
    ← (isSymmetric_of_isHermitian hA) (eigBasis hA i) x, toEuclideanLin_eigBasis,
    real_inner_smul_left]

/-- The quadratic form in the eigenbasis. -/
lemma quad_eq_sum (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin m)) :
    quad A x = ∑ i, sortedEig A i * ((eigBasis hA).repr x i) ^ 2 := by
  have h := (eigBasis hA).repr.inner_map_map x (Matrix.toEuclideanLin A x)
  rw [quad, ← h, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [repr_toEuclideanLin]
  simp [RCLike.inner_apply]
  ring

/-- Parseval for the eigenbasis. -/
lemma norm_sq_eq_sum (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin m)) :
    ‖x‖ ^ 2 = ∑ i, ((eigBasis hA).repr x i) ^ 2 := by
  have h := (eigBasis hA).repr.norm_map x
  rw [← h, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

/-- Lower bound on the span of the first `k+1` eigenvectors. -/
lemma quad_ge_of_upper (hA : A.IsHermitian) (k : Fin m) {x : EuclideanSpace ℝ (Fin m)}
    (hx : ∀ i, k < i → (eigBasis hA).repr x i = 0) :
    sortedEig A k * ‖x‖ ^ 2 ≤ quad A x := by
  rw [quad_eq_sum hA, norm_sq_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_or_gt i k with hik | hik
  · exact mul_le_mul_of_nonneg_right (sortedEig_antitone A hik) (sq_nonneg _)
  · rw [hx i hik]
    simp

/-- Upper bound where the first `k` coordinates vanish. -/
lemma quad_le_of_lower (hA : A.IsHermitian) (k : Fin m) {x : EuclideanSpace ℝ (Fin m)}
    (hx : ∀ i, i < k → (eigBasis hA).repr x i = 0) :
    quad A x ≤ sortedEig A k * ‖x‖ ^ 2 := by
  rw [quad_eq_sum hA, norm_sq_eq_sum hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases le_or_gt k i with hik | hik
  · exact mul_le_mul_of_nonneg_right (sortedEig_antitone A hik) (sq_nonneg _)
  · rw [hx i hik]
    simp

/-! ## The dimension count -/

/-- Vectors whose eigen-coordinates vanish on a set of indices. -/
def coordKer (hA : A.IsHermitian) (S : Set (Fin m)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin m)) where
  carrier := {x | ∀ i ∈ S, (eigBasis hA).repr x i = 0}
  zero_mem' := by intro i _; simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro c x hx i hi
    simp [hx i hi]

/-- The span of the eigenvectors with index `≤ k`. -/
def upSpace (hA : A.IsHermitian) (k : Fin m) : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
  Submodule.span ℝ (Set.range fun i : {i : Fin m // i ≤ k} => eigBasis hA i)

lemma upSpace_le_coordKer (hA : A.IsHermitian) (k : Fin m) :
    upSpace hA k ≤ coordKer hA {i | k < i} := by
  rw [upSpace]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, rfl⟩ i hi
  have hij : i ≠ (j : Fin m) := fun h => absurd (h ▸ hi) (not_lt.2 j.2)
  rw [OrthonormalBasis.repr_self]
  simp [EuclideanSpace.single_apply, hij]

lemma finrank_upSpace (hA : A.IsHermitian) (k : Fin m) :
    Module.finrank ℝ (upSpace hA k) = (k : ℕ) + 1 := by
  have hli : LinearIndependent ℝ (fun i : {i : Fin m // i ≤ k} => eigBasis hA i) :=
    ((eigBasis hA).orthonormal.comp _ Subtype.val_injective).linearIndependent
  rw [upSpace, finrank_span_eq_card hli, Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Fin m => i ≤ k) = Finset.Iic k := by
    ext i
    simp
  rw [this, Fin.card_Iic]

/-- **The min–max exchange.**  There is a unit vector in the span of the first `k+1`
eigenvectors of `A` whose first `k` eigen-coordinates for `A'` vanish. -/
lemma exists_unit_vector {A' : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian)
    (hA' : A'.IsHermitian) (k : Fin m) :
    ∃ x : EuclideanSpace ℝ (Fin m), ‖x‖ = 1 ∧
      (∀ i, k < i → (eigBasis hA).repr x i = 0) ∧
      (∀ i, i < k → (eigBasis hA').repr x i = 0) := by
  classical
  -- the first `k` coordinates in the eigenbasis of `A'`, restricted to `upSpace hA k`
  set f : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] ({i : Fin m // i < k} → ℝ) :=
    { toFun := fun x i => (eigBasis hA').repr x i
      map_add' := by intro x y; funext i; simp
      map_smul' := by intro c x; funext i; simp } with hf
  set g := f.domRestrict (upSpace hA k) with hg
  have hrange : Module.finrank ℝ (LinearMap.range g) ≤ (k : ℕ) := by
    refine le_trans (Submodule.finrank_le _) ?_
    rw [Module.finrank_pi ℝ, Fintype.card_subtype]
    have : (Finset.univ.filter fun i : Fin m => i < k) = Finset.Iio k := by
      ext i
      simp
    rw [this, Fin.card_Iio]
  have hker : 0 < Module.finrank ℝ (LinearMap.ker g) := by
    have hsum := LinearMap.finrank_range_add_finrank_ker g
    rw [finrank_upSpace hA k] at hsum
    omega
  have hnt : Nontrivial (LinearMap.ker g) := Module.finrank_pos_iff.1 hker
  obtain ⟨y, hy0⟩ := exists_ne (0 : LinearMap.ker g)
  have hyU : (y : EuclideanSpace ℝ (Fin m)) ∈ upSpace hA k := y.1.2
  have hyne : (y : EuclideanSpace ℝ (Fin m)) ≠ 0 := by
    intro h
    exact hy0 (Subtype.ext (Subtype.ext h))
  have hynorm : ‖(y : EuclideanSpace ℝ (Fin m))‖ ≠ 0 := norm_ne_zero_iff.2 hyne
  refine ⟨‖(y : EuclideanSpace ℝ (Fin m))‖⁻¹ • (y : EuclideanSpace ℝ (Fin m)), ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm]
    field_simp
  · intro i hik
    rw [map_smul]
    simp [upSpace_le_coordKer hA k hyU i hik]
  · intro i hik
    rw [map_smul]
    have hzero : (eigBasis hA').repr (y : EuclideanSpace ℝ (Fin m)) i = 0 := by
      have hy : g (y : ↥(upSpace hA k)) = 0 := LinearMap.mem_ker.1 y.2
      exact congrFun hy ⟨i, hik⟩
    simp [hzero]

/-! ## Weyl's inequality -/

/-- One half of Weyl's inequality for the sorted eigenvalues. -/
theorem sortedEig_sub_le_opNorm {A' : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian)
    (hA' : A'.IsHermitian) (k : Fin m) :
    sortedEig A k - sortedEig A' k ≤ opNorm (A' - A) := by
  obtain ⟨x, hx1, hxA, hxA'⟩ := exists_unit_vector hA hA' k
  have h1 : sortedEig A k ≤ quad A x := by
    have := quad_ge_of_upper hA k hxA
    rwa [hx1, one_pow, mul_one] at this
  have h2 : quad A' x ≤ sortedEig A' k := by
    have := quad_le_of_lower hA' k hxA'
    rwa [hx1, one_pow, mul_one] at this
  have h3 : |quad (A' - A) x| ≤ opNorm (A' - A) := by
    have := abs_quad_le (A' - A) x
    rwa [hx1, one_pow, mul_one] at this
  have h4 : quad (A' - A) x = quad A' x - quad A x := quad_sub _ _ _
  have h5 : quad A x - quad A' x ≤ opNorm (A' - A) := by
    have hneg : -(quad A' x - quad A x) ≤ |quad (A' - A) x| := by
      rw [h4]
      exact neg_le_abs _
    linarith
  linarith


/-! ## `Fact2_Weyl` -/

/-- Reindexing a family by a bijection does not change the multiset of its values. -/
lemma multiset_map_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : β → ℝ)
    (g : α ≃ β) :
    Multiset.map (fun i => f (g i)) Finset.univ.val = Multiset.map f Finset.univ.val := by
  have hcomp : (fun i => f (g i)) = f ∘ g := rfl
  rw [hcomp, ← Multiset.map_map]
  congr 1
  have h := congrArg Finset.val (Finset.map_univ_equiv g)
  rw [Finset.map_val] at h
  simpa using h

/-- Any antitone rearrangement of the eigenvalues *is* the sorted eigenvalue function. -/
lemma eq_sortedEig_of_antitone {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} (hA : A.IsHermitian)
    {σ : Fin m → ℝ} (hmono : Antitone σ) {e : Fin m ≃ Fin m}
    (hσ : σ = fun i => hA.eigenvalues (e i)) : σ = sortedEig A := by
  classical
  refine List.ofFn_injective ?_
  refine List.Perm.eq_of_pairwise' (r := (· ≥ ·))
    (List.sortedGE_iff_pairwise.1 hmono.sortedGE_ofFn)
    (List.sortedGE_iff_pairwise.1 (sortedEig_antitone A).sortedGE_ofFn) ?_
  rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map, hσ]
  have h1 : Multiset.map (fun i => hA.eigenvalues (e i)) Finset.univ.val =
      Multiset.map hA.eigenvalues Finset.univ.val := multiset_map_equiv _ e
  have h2 : Multiset.map hA.eigenvalues Finset.univ.val =
      Multiset.map hA.eigenvalues₀ Finset.univ.val := by
    have h : hA.eigenvalues = fun i : Fin m =>
        hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i) := rfl
    rw [h]
    exact multiset_map_equiv _ _
  have h3 : Multiset.map (sortedEig A) Finset.univ.val =
      Multiset.map hA.eigenvalues₀ Finset.univ.val := by
    have : sortedEig A = fun j : Fin m => hA.eigenvalues₀ (finCongr (Fintype.card_fin m).symm j) :=
      funext fun j => sortedEig_of_isHermitian hA j
    rw [this]
    exact multiset_map_equiv _ (finCongr (Fintype.card_fin m).symm)
  rw [h1, h2, h3]

lemma opNorm_sub_comm (A B : Matrix (Fin m) (Fin m) ℝ) : opNorm (A - B) = opNorm (B - A) := by
  have h : A - B = -(B - A) := by abel
  rw [opNorm, opNorm, h, map_neg, norm_neg]

/-- **Fact 2, proved.**  Weyl's eigenvalue perturbation inequality: the sorted eigenvalues of
a real symmetric matrix are 1-Lipschitz in the operator norm. -/
theorem fact2_weyl (m : ℕ) : Fact2_Weyl m := by
  intro A A' hA hA' σ σ' e e' hmono hmono' hσ hσ' i
  have h1 : σ = sortedEig A := eq_sortedEig_of_antitone hA hmono hσ
  have h2 : σ' = sortedEig A' := eq_sortedEig_of_antitone hA' hmono' hσ'
  rw [h1, h2, abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have := sortedEig_sub_le_opNorm hA' hA i
    rw [opNorm_sub_comm] at this
    linarith
  · exact sortedEig_sub_le_opNorm hA hA' i


end PCError

end
